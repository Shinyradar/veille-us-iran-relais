# -*- coding: utf-8 -*-
"""
Radar « Veille US-Iran »

Surveille en continu des sources fiables (agences, grands médias, sources officielles,
alertes missiles en Israël, conseils aux voyageurs) sur la situation
États-Unis / Iran / Israël / Dubaï-Golfe.

  - écrit tout ce qui est pertinent dans le journal (alertes/AAAA-MM-JJ.md et radar/donnees/fil.jsonl)
  - met à jour tableau-de-bord.html (fil en direct)
  - envoie les alertes importantes sur le téléphone (ntfy) et en notification Windows.

Usage :
  python radar.py                  boucle continue (lancé au démarrage du PC)
  python radar.py --essai          un passage sans rien envoyer ni écrire : affiche ce qui serait détecté
  python radar.py --une-fois       un passage réel puis arrêt (utilisé par le relais internet)
  python radar.py --test-notif     envoie une notification de test sur le téléphone et le PC
  python radar.py --depuis 65      liste ce qui a été détecté ces 65 dernières minutes (pour l'analyse Claude)
  python radar.py --etat           état du radar et des sources
"""
from __future__ import annotations

import argparse
import base64
import calendar
import hashlib
import html
import json
import logging
import os
import random
import re
import socket
import string
import subprocess
import sys
import threading
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
from collections import deque
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
from logging.handlers import RotatingFileHandler
from pathlib import Path

try:
    import feedparser
except ImportError:  # pragma: no cover
    sys.stderr.write("Module manquant : lance  python -m pip install --user feedparser\n")
    raise

RADAR = Path(__file__).resolve().parent
RACINE = RADAR.parent
ETAT = RADAR / "etat"
DONNEES = RADAR / "donnees"
ALERTES = RACINE / "alertes"
TABLEAU = RACINE / "tableau-de-bord.html"
FIL = DONNEES / "fil.jsonl"

UA_NAVIGATEUR = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                 "(KHTML, like Gecko) Chrome/130.0 Safari/537.36")
UA_RADAR = "VeilleUSIran/1.0"
PORT_VERROU = 48731

RANG = {"bleu": 1, "orange": 2, "rouge": 3}
EMOJI = {"rouge": "🔴", "orange": "🟠", "bleu": "🔵"}
NOM_NIVEAU = {"rouge": "Urgent", "orange": "Important", "bleu": "Info"}
ETIQUETTES = {
    "confirme": "✅ Confirmé",
    "une_source": "⚠️ Une seule source",
    "rapporte": "⚠️ Rapporté, non vérifié",
    "officiel": "🏛️ Déclaration officielle",
    "etat_iran": "🏛️ Média d'État iranien",
    "opposition": "⚠️ Média d'opposition",
}

DEFAUTS = {
    "ntfy_serveur": "https://ntfy.sh",
    "ntfy_sujet": "",
    "notifications_telephone": True,
    "notifications_windows": True,
    "priorite": {"rouge": 5, "orange": 3, "confirmation": 4, "resume": 3},
    "pousser_orange": True,
    "orange_max_par_heure": 4,
    "orange_fiabilites": ["A", "O"],
    "age_max_push_minutes": 90,
    "max_push_par_passage": 6,
    "tzevaadom_seuil_localites": 40,
    "fenetre_regroupement_heures": 3,
    "traduire": True,
}

JOURS = ["lundi", "mardi", "mercredi", "jeudi", "vendredi", "samedi", "dimanche"]
MOIS = ["janvier", "février", "mars", "avril", "mai", "juin", "juillet", "août",
        "septembre", "octobre", "novembre", "décembre"]

log = logging.getLogger("radar")


# --------------------------------------------------------------------------- outils

def lire_json(chemin: Path, defaut=None):
    try:
        return json.loads(chemin.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return {} if defaut is None else defaut
    except Exception as ex:  # fichier abîmé : on repart proprement
        log.warning("Fichier illisible %s (%s), réinitialisé", chemin.name, ex)
        return {} if defaut is None else defaut


def ecrire_json(chemin: Path, donnees) -> None:
    tmp = chemin.with_suffix(chemin.suffix + ".tmp")
    tmp.write_text(json.dumps(donnees, ensure_ascii=False, indent=1), encoding="utf-8")
    os.replace(tmp, chemin)


def empreinte(texte: str) -> str:
    return hashlib.sha1(texte.encode("utf-8", "replace")).hexdigest()[:16]


def decalage_paris(ts: float) -> int:
    """Heure d'été européenne : du dernier dimanche de mars au dernier dimanche d'octobre, 01:00 UTC."""
    d = datetime.fromtimestamp(ts, tz=timezone.utc)

    def dernier_dimanche(mois: int) -> datetime:
        x = datetime(d.year, mois, 31, 1, tzinfo=timezone.utc)
        while x.weekday() != 6:
            x -= timedelta(days=1)
        return x

    return 2 if dernier_dimanche(3) <= d < dernier_dimanche(10) else 1


def paris(ts: float) -> datetime:
    return datetime.fromtimestamp(ts + decalage_paris(ts) * 3600, tz=timezone.utc)


def heure_paris(ts: float) -> str:
    return paris(ts).strftime("%H:%M")


def jour_paris(ts: float) -> str:
    return paris(ts).strftime("%Y-%m-%d")


def jour_long(ts: float) -> str:
    d = paris(ts)
    return f"{JOURS[d.weekday()]} {d.day} {MOIS[d.month - 1]} {d.year}"


def texte_brut(fragment: str) -> str:
    t = re.sub(r"<(script|style)[^>]*>.*?</\1>", " ", fragment or "", flags=re.S | re.I)
    t = re.sub(r"<br\s*/?>|</p>|</div>|</li>", " ", t, flags=re.I)
    t = re.sub(r"<[^>]+>", " ", t)
    t = html.unescape(t)
    return re.sub(r"\s+", " ", t).strip()


RX_US = re.compile(r"\bU\.S\.(?:A\.)?|\bUSA\b|\bUS\b")
RX_EAU = re.compile(r"\bEAU\b")
RX_PROXY = re.compile(
    r"\b(?:iran|iranian)[- ](?:backed|aligned|allied|sponsored|funded|linked|supported)\b"
    r"|\bsoutenus? par (?:l')?iran\b|\bpro-?iranien(?:ne)?s?\b|\bpro-?iran\b"
    r"|\ballies? de (?:l')?iran\b|\bproches? de (?:l')?iran\b|\bfinance(?:e|s|es)? par (?:l')?iran\b"
    r"|\barmes? par (?:l')?iran\b")


# Intitulés de rubrique en début de titre (« Iran war: », « US/Israel-Iran war latest: », « Guerre en Iran : »)
RX_RUBRIQUE = re.compile(
    r"^\W*(?:live(?: updates?)?\W+)?(?:(?:usa|israel)\W*){0,2}(?:iran|middle east|mideast|gulf)\W+(?:war|crisis|conflict)"
    r"(?:\W+(?:latest|live|news|updates?))?\s*[:|\-]\s*"
    r"|^\W*guerre (?:en |contre l'|au )?(?:iran|moyen-orient|proche-orient)\s*[:\-]\s*")


def normaliser(texte: str) -> str:
    t = (texte or "").replace("’", "'").replace("‘", "'").replace("‐", "-").replace("–", "-")
    t = RX_US.sub(" usa ", t)
    t = RX_EAU.sub(" emirats ", t)
    t = "".join(c for c in unicodedata.normalize("NFKD", t) if not unicodedata.combining(c)).lower()
    t = RX_PROXY.sub(" proxy ", t)
    return re.sub(r"\s+", " ", t)


MOTS_VIDES = set("""the a an of to in on for and or with at by from as is are was were be been has have had it its
this that after over into amid says said say new about than more not but will his her their they he she what who
le la les de des du un une et ou en au aux pour par sur dans avec selon apres contre est sont ete plus qui que ne pas
son sa ses leur leurs ce cette ces il elle ils elles lors face entre""".split())
SYNONYMES = {
    "iranian": "iran", "iranians": "iran", "iranien": "iran", "iranienne": "iran", "iraniens": "iran",
    "iraniennes": "iran", "teheran": "tehran", "israeli": "israel", "israelis": "israel", "israelien": "israel",
    "israelienne": "israel", "israeliens": "israel", "israeliennes": "israel", "american": "usa",
    "americans": "usa", "americain": "usa", "americaine": "usa", "americains": "usa", "etats-unis": "usa",
    "washington": "usa", "strikes": "strike", "struck": "strike", "striking": "strike", "frappe": "strike",
    "frappes": "strike", "attacks": "attack", "attacked": "attack", "attaque": "attack", "attaques": "attack",
    "missiles": "missile", "drones": "drone", "killed": "kill", "kills": "kill", "tue": "kill", "tues": "kill",
    "tuee": "kill", "tuees": "kill", "talks": "talks", "negotiations": "talks", "negociations": "talks",
    "pourparlers": "talks", "agreement": "deal", "accord": "deal", "sanctions": "sanction",
    "sanctioned": "sanction", "tanker": "ship", "tankers": "ship", "vessel": "ship", "vessels": "ship",
    "ships": "ship", "navire": "ship", "navires": "ship", "petrolier": "ship", "petroliers": "ship",
    "ormuz": "hormuz", "nucleaire": "nuclear", "emirats": "uae", "emirati": "uae", "dubai": "dubai",
    "etats": "usa",
}
MOTS_VIDES.update({"unis", "related", "linked", "report", "reports", "news"})
# Les mois ne disent rien de l'événement : sans ça, deux alertes d'ambassade différentes datées de novembre
# 2026 étaient prises pour la même info.
MOTS_VIDES.update("""january february march april june july august september october november december
janvier fevrier mars avril juin juillet aout septembre octobre novembre decembre""".split())


def jetons(titre: str) -> set:
    t = re.sub(r"[^a-z0-9 ]", " ", normaliser(titre))
    out = set()
    for m in t.split():
        if (len(m) < 3 and m != "us") or m.isdigit():  # chiffres (années, jours) exclus
            continue
        m = SYNONYMES.get(m, m)
        if m in MOTS_VIDES:
            continue
        if len(m) > 4 and m.endswith("s") and not m.endswith("ss"):
            m = m[:-1]
        out.add(m)
    return out


def similaires(a: set, b: set) -> bool:
    if not a or not b:
        return False
    inter = len(a & b)
    return inter / len(a | b) >= 0.5 or inter >= 5


def lien_sur(url: str) -> str:
    return url if isinstance(url, str) and url.startswith(("http://", "https://")) else ""


# --------------------------------------------------------------------------- règles

class Regles:
    def __init__(self, donnees: dict):
        self.groupes = {k: re.compile("|".join(f"(?:{p})" for p in v)) for k, v in donnees["groupes"].items()}
        self.acteurs = set(donnees["acteurs"])
        self.pertinence = donnees["pertinence"]
        self.rouge = donnees["rouge"]
        self.orange = donnees["orange"]
        self.categories = donnees["categories"]
        self.plafonds = donnees.get("plafonds", [])
        self.plafond_fiab = donnees.get("plafond_par_fiabilite", {})

    def sujets(self, texte_norm: str) -> set:
        return {k for k, rx in self.groupes.items() if rx.search(texte_norm)}

    @staticmethod
    def _combo(sujets: set, combos) -> bool:
        return any(all(g in sujets for g in c) for c in combos)

    def pertinent(self, sujets: set) -> bool:
        return self._combo(sujets, self.pertinence)

    def niveau(self, sujets_titre: set, fiab: str | None = None) -> str:
        n = "bleu"
        if self._combo(sujets_titre, self.orange):
            n = "orange"
        if self._combo(sujets_titre, self.rouge):
            n = "rouge"
        if n != "bleu" and "attenuants" in sujets_titre:
            n = "orange" if n == "rouge" else "bleu"
        for p in self.plafonds:
            if p["groupe"] in sujets_titre and not any(g in sujets_titre for g in p.get("sauf", [])):
                if RANG[n] > RANG[p["max"]]:
                    n = p["max"]
        plafond = self.plafond_fiab.get(fiab or "")
        if plafond and RANG[n] > RANG[plafond]:
            n = plafond
        return n

    def categorie(self, sujets_titre: set) -> str:
        for groupe, libelle in self.categories:
            if groupe in sujets_titre:
                return libelle
        return "Actualité"


def etiquette_cluster(directs: dict) -> str:
    """directs = éditeurs dont le titre affirme le fait lui-même (pas « selon l'agence iranienne… »)."""
    if not directs:
        return "rapporte"
    f = list(directs.values())
    nb_b = sum(1 for x in f if x == "B")
    nb_o = sum(1 for x in f if x == "O")
    if "A" in f or nb_b >= 2 or (nb_b >= 1 and nb_o >= 1):
        return "confirme"
    if nb_b:
        return "une_source"
    if nb_o:
        return "officiel"
    if "E" in f:
        return "etat_iran"
    return "opposition"


# --------------------------------------------------------------------------- réseau

def telecharger(url: str, entetes: dict | None = None, timeout: int = 20, ua: str = UA_NAVIGATEUR):
    h = {"User-Agent": ua, "Accept": "*/*", "Accept-Language": "fr,en;q=0.8"}
    if entetes:
        h.update({k: v for k, v in entetes.items() if v})
    req = urllib.request.Request(url, headers=h)
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return r.status, r.read(), r.headers
    except urllib.error.HTTPError as e:
        if e.code == 304:
            return 304, b"", e.headers
        raise


def parser_telegram(page: str) -> list:
    entrees = []
    for bloc in page.split('data-post="')[1:]:
        post = bloc.split('"', 1)[0]
        m_txt = re.search(r'<div class="tgme_widget_message_text[^"]*"[^>]*>(.*?)</div>', bloc, re.S)
        if not m_txt:
            continue
        texte = texte_brut(m_txt.group(1))
        if not texte:
            continue
        ts = None
        m_t = re.search(r'<time[^>]+datetime="([^"]+)"', bloc)
        if m_t:
            try:
                ts = datetime.fromisoformat(m_t.group(1)).timestamp()
            except ValueError:
                ts = None
        titre = texte if len(texte) <= 220 else texte[:217].rsplit(" ", 1)[0] + "…"
        entrees.append({"titre": titre, "lien": f"https://t.me/{post}", "resume": texte[:700],
                        "ts_pub": ts, "src_titre": "", "src_href": ""})
    return entrees


# --------------------------------------------------------------------------- configuration

def charger_config() -> dict:
    chemin = RADAR / "config.json"
    if not chemin.exists():
        alea = random.SystemRandom()
        sujet = "veille-us-iran-" + "".join(alea.choice(string.ascii_lowercase + string.digits) for _ in range(14))
        cfg = dict(DEFAUTS, ntfy_sujet=sujet)
        cfg["_lisezmoi"] = ("ntfy_sujet = nom secret de ton canal ntfy (à saisir dans l'appli ntfy). "
                            "priorite : 5 = urgent (sonne fort), 3 = normal. pousser_orange : false pour ne recevoir que les alertes rouges.")
        chemin.write_text(json.dumps(cfg, ensure_ascii=False, indent=2), encoding="utf-8")
    cfg = dict(DEFAUTS)
    cfg.update(lire_json(chemin))
    if os.environ.get("NTFY_SUJET"):
        cfg["ntfy_sujet"] = os.environ["NTFY_SUJET"].strip()
    return cfg


def configurer_journal(console: bool) -> None:
    ETAT.mkdir(parents=True, exist_ok=True)
    log.setLevel(logging.INFO)
    fmt = logging.Formatter("%(asctime)s %(levelname)s %(message)s", "%Y-%m-%d %H:%M:%S")
    fh = RotatingFileHandler(ETAT / "radar.log", maxBytes=1_000_000, backupCount=3, encoding="utf-8")
    fh.setFormatter(fmt)
    log.addHandler(fh)
    if console and sys.stdout:
        sh = logging.StreamHandler(sys.stdout)
        sh.setFormatter(fmt)
        log.addHandler(sh)


# --------------------------------------------------------------------------- notifications

PS_TOAST = r"""
[Windows.UI.Notifications.ToastNotificationManager, Windows.UI.Notifications, ContentType = WindowsRuntime] > $null
[Windows.Data.Xml.Dom.XmlDocument, Windows.Data.Xml.Dom.XmlDocument, ContentType = WindowsRuntime] > $null
$d = { param($b) [System.Text.Encoding]::UTF8.GetString([Convert]::FromBase64String($b)) }
$t = [System.Security.SecurityElement]::Escape((& $d '__T__'))
$m = [System.Security.SecurityElement]::Escape((& $d '__M__'))
$l = [System.Security.SecurityElement]::Escape((& $d '__L__'))
$x = New-Object Windows.Data.Xml.Dom.XmlDocument
$a = ''
if ($l) { $a = " activationType='protocol' launch='$l'" }
$x.LoadXml("<toast$a><visual><binding template='ToastGeneric'><text>$t</text><text>$m</text></binding></visual></toast>")
$n = [Windows.UI.Notifications.ToastNotification]::new($x)
[Windows.UI.Notifications.ToastNotificationManager]::CreateToastNotifier('{1AC14E77-02E7-4E5D-B744-2EB1AE5198B7}\WindowsPowerShell\v1.0\powershell.exe').Show($n)
"""


def notification_windows(titre: str, message: str, lien: str = "") -> None:
    if os.name != "nt":
        return
    b64 = lambda s: base64.b64encode((s or "").encode("utf-8")).decode("ascii")
    script = PS_TOAST.replace("__T__", b64(titre)).replace("__M__", b64(message)).replace("__L__", b64(lien))
    try:
        subprocess.Popen(["powershell.exe", "-NoProfile", "-NonInteractive", "-WindowStyle", "Hidden",
                          "-ExecutionPolicy", "Bypass", "-Command", script],
                         creationflags=0x08000000, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    except Exception as ex:
        log.warning("Notification Windows impossible : %s", ex)


def envoyer_ntfy(cfg: dict, titre: str, message: str, priorite: int, lien: str = "", tags=None) -> None:
    corps = {"topic": cfg["ntfy_sujet"], "title": titre, "message": message, "priority": int(priorite)}
    if lien:
        corps["click"] = lien
    if tags:
        corps["tags"] = tags
    req = urllib.request.Request(cfg["ntfy_serveur"].rstrip("/") + "/",
                                 data=json.dumps(corps, ensure_ascii=False).encode("utf-8"),
                                 headers={"Content-Type": "application/json", "User-Agent": UA_RADAR},
                                 method="POST")
    with urllib.request.urlopen(req, timeout=15) as r:
        r.read()


# --------------------------------------------------------------------------- relais internet

def trouver_gh():
    candidats = [Path(os.environ.get("LOCALAPPDATA", "")) / "Programs" / "GitHubCLI" / "bin" / "gh.exe",
                 Path(r"C:\Program Files\GitHub CLI\gh.exe")]
    for p in candidats:
        if p.exists():
            return str(p)
    import shutil
    return shutil.which("gh")


# --------------------------------------------------------------------------- traduction

URL_TRADUCTION = "https://translate.googleapis.com/translate_a/single?client=gtx&sl=auto&tl=fr&dt=t&q="


class Traducteur:
    """Traduit les titres en français (Google Traduction, sans clé). En cas d'échec : titre original."""

    def __init__(self, actif: bool = True):
        self.actif = actif
        brut = lire_json(ETAT / "traductions.json", {})
        self.cache = {k: v for k, v in brut.items() if isinstance(v, list) and len(v) == 2}
        self.lock = threading.Lock()
        self.lock_requete = threading.Lock()
        self.derniere_requete = 0.0
        self.echecs = 0
        self.pause_jusqua = 0.0

    def traduire(self, texte: str):
        if not self.actif or not texte:
            return None
        cle = empreinte(texte)
        with self.lock:
            if cle in self.cache:
                return self.cache[cle][0]
        if time.time() < self.pause_jusqua:
            return None
        try:
            with self.lock_requete:  # au plus ~3 requêtes par seconde, pour ne pas se faire bloquer
                attente = self.derniere_requete + 0.35 - time.time()
                if attente > 0:
                    time.sleep(attente)
                self.derniere_requete = time.time()
                _, data, _ = telecharger(URL_TRADUCTION + urllib.parse.quote(texte[:1000]), timeout=10)
            j = json.loads(data.decode("utf-8"))
            fr = "".join(seg[0] for seg in (j[0] or []) if seg and seg[0]).strip()
            langue = j[2] if len(j) > 2 else None
            if not fr or langue == "fr":
                fr = texte
            with self.lock:
                self.cache[cle] = [fr, time.time()]
            self.echecs = 0
            return fr
        except Exception as ex:
            self.echecs += 1
            self.pause_jusqua = time.time() + min(30 * (2 ** self.echecs), 3600)
            if self.echecs in (1, 5, 20):
                log.warning("Traduction indisponible (%s) : titres laissés en version originale pour l'instant", ex)
            return None

    def sauver(self) -> None:
        limite = time.time() - 8 * 86400
        with self.lock:
            self.cache = {k: v for k, v in self.cache.items() if v[1] >= limite}
            copie = dict(self.cache)
        ecrire_json(ETAT / "traductions.json", copie)


# --------------------------------------------------------------------------- tableau de bord

MODELE_TABLEAU = r"""<!doctype html>
<html lang="fr"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Veille US-Iran</title>
<style>
:root{--fond:#f5f6f8;--carte:#ffffff;--texte:#15171c;--doux:#5d6472;--bord:#e2e5ea;--rouge:#d92d20;--orange:#dc6c00;--bleu:#2f6bd6;--lien:#1d4ed8;--alerte-fond:#fff4d6;--alerte-texte:#5c4400}
@media (prefers-color-scheme:dark){:root{--fond:#0f1115;--carte:#171a21;--texte:#e8eaee;--doux:#9aa3b2;--bord:#2a2f3a;--rouge:#ff6b5e;--orange:#ffa53d;--bleu:#7aa5ff;--lien:#8fb6ff;--alerte-fond:#3a2f0b;--alerte-texte:#ffe08a}}
*{box-sizing:border-box}
body{margin:0;background:var(--fond);color:var(--texte);font:15px/1.45 system-ui,-apple-system,"Segoe UI",Roboto,sans-serif}
header{position:sticky;top:0;z-index:2;background:var(--fond);border-bottom:1px solid var(--bord);padding:12px 16px}
.int{max-width:980px;margin:0 auto}
h1{font-size:18px;margin:0 0 2px}
.etat{color:var(--doux);font-size:13px}
.barre{display:flex;flex-wrap:wrap;gap:8px;margin-top:10px;align-items:center}
.puce{border:1px solid var(--bord);background:var(--carte);color:var(--texte);border-radius:999px;padding:4px 12px;cursor:pointer;font:inherit;font-size:13px}
.puce.actif{border-color:var(--texte);font-weight:600}
.n{color:var(--doux);font-weight:400}
input[type=search]{flex:1;min-width:150px;border:1px solid var(--bord);background:var(--carte);color:var(--texte);border-radius:8px;padding:6px 10px;font:inherit;font-size:14px}
main{max-width:980px;margin:0 auto;padding:4px 16px 48px}
.jour{margin:20px 0 6px;font-size:12.5px;text-transform:uppercase;letter-spacing:.05em;color:var(--doux)}
.it{background:var(--carte);border:1px solid var(--bord);border-left:4px solid var(--bleu);border-radius:8px;padding:9px 12px;margin:6px 0}
.it.rouge{border-left-color:var(--rouge)}.it.orange{border-left-color:var(--orange)}
.meta{font-size:12.5px;color:var(--doux);display:flex;flex-wrap:wrap;gap:4px 12px}
.t{font-weight:600;margin:3px 0;overflow-wrap:anywhere}
.t a{color:var(--texte);text-decoration:none}.t a:hover{text-decoration:underline}
.vo{font-size:12px;color:var(--doux);margin:-1px 0 3px;overflow-wrap:anywhere}
.src a{color:var(--lien);text-decoration:none;font-size:12.5px;margin-right:10px;white-space:nowrap}
.vide{color:var(--doux);padding:30px 0;text-align:center}
.alerte{background:var(--alerte-fond);color:var(--alerte-texte);border-radius:8px;padding:8px 12px;margin-top:8px;font-size:13px}
.pied{color:var(--doux);font-size:12px;margin-top:24px}
</style></head><body>
<header><div class="int">
<h1>🛰️ Veille US-Iran — fil en direct</h1>
<div class="etat" id="etat"></div>
<div id="alerte"></div>
<div class="barre">
<button class="puce" data-f="tout">Tout <span class="n" id="n-tout"></span></button>
<button class="puce" data-f="rouge">🔴 Urgent <span class="n" id="n-rouge"></span></button>
<button class="puce" data-f="orange">🟠 Important <span class="n" id="n-orange"></span></button>
<button class="puce" data-f="bleu">🔵 Info <span class="n" id="n-bleu"></span></button>
<input type="search" id="q" placeholder="Filtrer : Ormuz, Dubaï, AIEA, Qeshm…">
</div></div></header>
<main id="fil"></main>
<main><div class="pied">✅ confirmé (agence ou 2 sources) · ⚠️ une seule source ou non vérifié · 🏛️ déclaration officielle ou média d'État. Titres traduits automatiquement en français (VO = titre original). La page se recharge seule chaque minute quand tu es en haut de page.</div></main>
<script id="donnees" type="application/json">__DONNEES__</script>
<script>
const D = JSON.parse(document.getElementById('donnees').textContent);
const E = {rouge:'🔴', orange:'🟠', bleu:'🔵'};
const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const norm = s => String(s || '').toLowerCase().normalize('NFD').replace(/[̀-ͯ]/g, '');
let filtre = location.hash.slice(1) || 'tout';
let q = '';
try { q = sessionStorage.getItem('q') || ''; } catch (e) {}
const champ = document.getElementById('q');
champ.value = q;
function rendu() {
  document.querySelectorAll('.puce').forEach(b => b.classList.toggle('actif', b.dataset.f === filtre));
  const qq = norm(q.trim());
  const base = D.clusters.filter(c => !qq || c.recherche.includes(qq));
  for (const k of ['tout','rouge','orange','bleu']) {
    document.getElementById('n-' + k).textContent = base.filter(c => k === 'tout' || c.niveau === k).length;
  }
  let h = '', jour = '';
  for (const c of base) {
    if (filtre !== 'tout' && c.niveau !== filtre) continue;
    if (c.jour !== jour) { jour = c.jour; h += '<div class="jour">' + esc(jour) + '</div>'; }
    h += '<div class="it ' + c.niveau + '"><div class="meta"><span>' + E[c.niveau] + ' ' + esc(c.heure) + '</span><span>'
      + esc(c.etiquette) + '</span><span>' + esc(c.categorie) + '</span>' + (c.pousse ? '<span>📲 alerte envoyée</span>' : '')
      + '</div><div class="t">' + (c.lien ? '<a href="' + esc(c.lien) + '" target="_blank" rel="noopener">' + esc(c.titre) + '</a>' : esc(c.titre))
      + '</div>' + (c.vo ? '<div class="vo">VO : ' + esc(c.vo) + '</div>' : '') + '<div class="src">' + c.liens.map(l => l[1] ? '<a href="' + esc(l[1]) + '" target="_blank" rel="noopener">' + esc(l[0]) + '</a>' : '<span>' + esc(l[0]) + '</span>').join('') + '</div></div>';
  }
  document.getElementById('fil').innerHTML = h || '<div class="vide">Rien pour ce filtre.</div>';
}
document.querySelectorAll('.puce').forEach(b => b.onclick = () => { filtre = b.dataset.f; history.replaceState(null, '', '#' + filtre); rendu(); });
champ.oninput = () => { q = champ.value; try { sessionStorage.setItem('q', q); } catch (e) {} rendu(); };
const age = Math.round((Date.now() / 1000 - D.genere) / 60);
document.getElementById('etat').textContent = 'Mis à jour à ' + D.heure + ' (heure de Paris) · ' + D.sources_ok + '/' + D.sources_total + ' sources répondent · ' + D.clusters.length + ' infos sur 72 h';
if (age > 10) document.getElementById('alerte').innerHTML = '<div class="alerte">⚠️ Le radar ne semble plus tourner : dernière mise à jour il y a ' + age + ' min. Relance-le avec « demarrer-radar.vbs » dans le dossier radar.</div>';
rendu();
setInterval(() => { if (window.scrollY < 80 && document.activeElement !== champ) location.reload(); }, 60000);
</script></body></html>"""


# --------------------------------------------------------------------------- radar

class Radar:
    def __init__(self, mode: str = "continu"):
        self.mode = mode
        self.essai = mode == "essai"
        self.cfg = charger_config()
        donnees_sources = lire_json(RADAR / "sources.json")
        self.sources = [s for s in donnees_sources["sources"] if s.get("actif", True)]
        if mode == "une_fois":  # relais internet : pas de sirènes (temps réel) ni de pages
            self.sources = [s for s in self.sources if s["type"] in ("rss", "gn", "telegram")]
        self.src_par_id = {s["id"]: s for s in self.sources}
        self.editeurs = {d.lower(): (v[0], v[1]) for d, v in donnees_sources.get("editeurs_reconnus", {}).items()}
        self.regles = Regles(lire_json(RADAR / "regles.json"))
        for d in (ETAT, DONNEES, ALERTES):
            d.mkdir(parents=True, exist_ok=True)
        self.amorcage = (not (ETAT / "vus.json").exists()) and not self.essai
        self.vus = {} if self.essai else lire_json(ETAT / "vus.json", {})
        self.clusters = {} if self.essai else lire_json(ETAT / "clusters.json", {})
        for c in self.clusters.values():  # clés présentes d'avance : la traduction en tâche de fond ne fait que les remplir
            c.setdefault("titre_fr", None)
            c.setdefault("jetons_fr", [])
        self.pages = lire_json(ETAT / "pages.json", {})
        self.tz_vus = {}
        self.salve = None
        self.sante = lire_json(ETAT / "sante.json", {}).get("sources", {}) if not self.essai else {}
        maintenant = time.time()
        self.prochain = {s["id"]: maintenant + (random.uniform(0, 25) if s["type"] == "gn" else 0) for s in self.sources}
        self.erreurs = {s["id"]: 0 for s in self.sources}
        self.tentes = set()
        self.validateurs = {}
        self.en_cours = {}
        self.pool = ThreadPoolExecutor(max_workers=12)
        self.pousses = deque(maxlen=300)
        self.file_push = []
        self.hist_ntfy = []
        self.hist_ntfy_maj = 0
        self.modifie = False
        self.dernier_tableau = 0
        self.demarre = maintenant
        self.stats = {"items": 0, "rouge": 0, "orange": 0, "bleu": 0, "push": []}
        self.trad = Traducteur(actif=bool(self.cfg.get("traduire", True)))
        self.retraduction = None
        self.derniere_retraduction = 0.0
        # Relais internet : si le PC est allumé, le relais met seulement son état à jour, sans envoyer d'alerte
        self.silencieux = mode == "une_fois" and os.environ.get("RELAIS_SILENCIEUX", "0") == "1"
        self.dernier_pouls = 0.0

    # ------------------------------------------------------------ récupération (threads)

    def recuperer(self, s: dict) -> dict:
        t = s["type"]
        if t == "tzevaadom":
            _, data, _ = telecharger(s["url"], timeout=8, entetes={"Referer": "https://www.tzevaadom.co.il/"})
            txt = data.decode("utf-8", "replace").strip() or "[]"
            return {"type": t, "data": json.loads(txt)}
        v = self.validateurs.get(s["id"], {})
        code, data, h = telecharger(s["url"], timeout=25,
                                    entetes={"If-None-Match": v.get("etag"), "If-Modified-Since": v.get("lm")})
        if code == 304:
            return {"type": t, "entrees": [], "inchange": True}
        self.validateurs[s["id"]] = {"etag": h.get("ETag"), "lm": h.get("Last-Modified")}
        if t in ("rss", "gn"):
            f = feedparser.parse(data)
            if not f.entries and getattr(f, "bozo", False):
                raise ValueError(f"flux illisible ({type(f.bozo_exception).__name__})")
            entrees = []
            for e in f.entries[:120]:
                p = e.get("published_parsed") or e.get("updated_parsed")
                si = e.get("source") or {}
                entrees.append({"titre": e.get("title", ""), "lien": e.get("link", ""),
                                "resume": e.get("summary", "") if t == "rss" else "",
                                "ts_pub": calendar.timegm(p) if p else None,
                                "src_titre": si.get("title", "") if hasattr(si, "get") else "",
                                "src_href": si.get("href", "") if hasattr(si, "get") else ""})
            return {"type": t, "entrees": self.preparer(s, t, entrees)}
        if t == "telegram":
            return {"type": t, "entrees": self.preparer(s, t, parser_telegram(data.decode("utf-8", "replace")))}
        if t == "page":
            return {"type": t, "contenu": data.decode("utf-8", "replace")}
        raise ValueError(f"type de source inconnu : {t}")

    def preparer(self, s: dict, t: str, entrees: list) -> list:
        """Nettoie les entrées, identifie l'éditeur et traduit en français les titres nouveaux et pertinents."""
        sortie = []
        for e in entrees:
            if t == "gn":
                ed, fi = self.editeur_gn(s, e)
                if not ed:
                    continue
                titre = texte_brut(e["titre"])
                st = (e.get("src_titre") or "").strip()
                if st and titre.endswith(" - " + st):
                    titre = titre[: -(len(st) + 3)]
                resume = ""
            else:
                ed, fi = s["editeur"], s.get("fiabilite", "B")
                titre = texte_brut(e["titre"])
                resume = texte_brut(e.get("resume", ""))[:700]
            titre = titre[:300]
            e2 = {"titre": titre, "lien": e["lien"], "resume": resume, "ts_pub": e["ts_pub"],
                  "editeur": ed, "fiab": fi, "titre_fr": titre if s.get("langue") == "fr" else None}
            # Sur le relais internet, on ne traduit que les alertes au moment de les envoyer
            if e2["titre_fr"] is None and titre and self.trad.actif and self.mode != "une_fois":
                cle_t = "t:" + empreinte(normaliser(titre) + "|" + ed)
                if cle_t not in self.vus:
                    sujets = self.regles.sujets(normaliser(titre + " " + resume)) | set(s.get("acteurs_implicites", []))
                    if not s.get("filtrer", True) or self.regles.pertinent(sujets):
                        e2["titre_fr"] = self.trad.traduire(titre)
            sortie.append(e2)
        return sortie

    def retraduire(self) -> None:
        """En tâche de fond : traduit les titres restés en version originale (démarrage, panne de traduction)."""
        for c in list(self.clusters.values()):
            if c.get("titre_fr"):
                continue
            fr = self.trad.traduire(c["titre"])
            if fr is None:
                if time.time() < self.trad.pause_jusqua:
                    return
                continue
            c["titre_fr"] = fr
            self.modifie = True
            time.sleep(0.25)

    # ------------------------------------------------------------ intégration (fil principal)

    def editeur_gn(self, s: dict, e: dict):
        if s.get("editeur"):
            return s["editeur"], s.get("fiabilite", "B")
        dom = urllib.parse.urlparse(e.get("src_href") or "").netloc.lower()
        if dom.startswith("www."):
            dom = dom[4:]
        if not dom:
            return None, None
        for suffixe, valeur in self.editeurs.items():
            if dom == suffixe or dom.endswith("." + suffixe):
                return valeur
        return None, None

    def integrer(self, s: dict, res: dict) -> None:
        t = res["type"]
        if t == "tzevaadom":
            self.traiter_tzeva(s, res["data"])
            return
        if t == "page":
            self.traiter_page(s, res["contenu"])
            return
        for e in res["entrees"]:
            self.traiter(s, e["titre"], e["lien"], e["resume"], e["ts_pub"], e["editeur"], e["fiab"],
                         titre_fr=e.get("titre_fr"))

    def traiter(self, s, titre, lien, resume, ts_pub, editeur, fiab, niveau_force=None, categorie_force=None,
                titre_fr=None):
        maintenant = time.time()
        titre = texte_brut(titre)[:300]
        if not titre:
            return None
        lien = lien_sur(lien)
        cle_t = "t:" + empreinte(normaliser(titre) + "|" + editeur)
        cle_l = ("l:" + empreinte(lien)) if lien else None
        if cle_t in self.vus or (cle_l and cle_l in self.vus):
            return None
        self.vus[cle_t] = maintenant
        if cle_l:
            self.vus[cle_l] = maintenant
        self.modifie = True
        if not ts_pub or ts_pub > maintenant + 600:
            ts_pub = maintenant
        if maintenant - ts_pub > 72 * 3600:
            return None
        implicites = set(s.get("acteurs_implicites", []))
        sujets = self.regles.sujets(normaliser(titre + " " + (resume or ""))) | implicites
        if s.get("filtrer", True) and not niveau_force and not self.regles.pertinent(sujets):
            return None
        titre_niv = RX_RUBRIQUE.sub("", normaliser(titre).strip(), count=1)
        sujets_titre = self.regles.sujets(titre_niv) | implicites
        niveau = niveau_force or self.regles.niveau(sujets_titre, fiab)
        if s.get("niveau_min") and RANG[s["niveau_min"]] > RANG[niveau]:
            niveau = s["niveau_min"]
        categorie = categorie_force or self.regles.categorie(sujets_titre)
        if niveau_force or s.get("langue") == "fr":
            titre_fr = titre_fr or titre
        item = {"ts": maintenant, "ts_pub": ts_pub, "source": s["id"], "editeur": editeur, "fiab": fiab,
                "titre": titre, "titre_fr": titre_fr, "resume": (resume or "")[:500], "lien": lien, "niveau": niveau,
                "categorie": categorie, "sujets": sorted(sujets & self.regles.acteurs),
                "attribue": "attribution" in sujets_titre}
        c, nouveau = self.rattacher(item)
        item["cluster"] = c["id"]
        action = self.decider(item, c)
        if action:
            self.file_push.append((action, c["id"]))
            if action != "confirmation":
                c["pousse"] = action
            c["pousse_ts"] = maintenant
        item["etiquette"] = c["etiquette"]
        item["pousse"] = action
        self.stats["items"] += 1
        self.stats[niveau] += 1
        if not self.essai:
            with FIL.open("a", encoding="utf-8") as f:
                f.write(json.dumps(item, ensure_ascii=False) + "\n")
            if nouveau or action:
                self.journaliser(c, action, nouveau)
        else:
            self.stats.setdefault("exemples", []).append(item)
        return item

    def rattacher(self, item: dict):
        j = jetons(item["titre"])
        jfr = jetons(item["titre_fr"]) if item.get("titre_fr") else set()
        fenetre = self.cfg["fenetre_regroupement_heures"] * 3600
        cible = None
        for c in self.clusters.values():
            if item["ts"] - c["dernier"] > fenetre:
                continue
            if similaires(j, set(c["jetons"])) or (jfr and c.get("jetons_fr") and similaires(jfr, set(c["jetons_fr"]))):
                cible = c
                break
        nouveau = cible is None
        if nouveau:
            cid = empreinte(item["titre"] + str(item["ts"]))[:10]
            cible = {"id": cid, "jetons": sorted(j), "jetons_fr": sorted(jfr), "premier": item["ts"],
                     "dernier": item["ts"], "ts_pub": item["ts_pub"], "niveau": item["niveau"],
                     "categorie": item["categorie"], "titre": item["titre"], "titre_fr": item.get("titre_fr"),
                     "lien": item["lien"], "editeurs": {}, "liens": {},
                     "pousse": None, "pousse_etiquette": None, "amorcage": self.amorcage or self.silencieux}
            self.clusters[cid] = cible
        cible["dernier"] = item["ts"]
        cible["editeurs"][item["editeur"]] = item["fiab"]
        if not item.get("attribue"):
            cible.setdefault("directs", {})[item["editeur"]] = item["fiab"]
        if item["lien"] and item["editeur"] not in cible["liens"]:
            cible["liens"][item["editeur"]] = item["lien"]
        if RANG[item["niveau"]] > RANG[cible["niveau"]]:
            cible.update(niveau=item["niveau"], categorie=item["categorie"], titre=item["titre"],
                         titre_fr=item.get("titre_fr"), lien=item["lien"])
        elif item["fiab"] == "A" and RANG[item["niveau"]] == RANG[cible["niveau"]] and \
                cible["editeurs"].get(self._editeur_du_titre(cible)) != "A":
            cible.update(titre=item["titre"], titre_fr=item.get("titre_fr"), lien=item["lien"])
        if not cible.get("jetons_fr") and jfr:
            cible["jetons_fr"] = sorted(jfr)
        cible["etiquette"] = etiquette_cluster(cible.get("directs") or {})
        return cible, nouveau

    @staticmethod
    def _editeur_du_titre(c: dict):
        for ed, l in c.get("liens", {}).items():
            if l == c.get("lien"):
                return ed
        return None

    def decider(self, item: dict, c: dict):
        if self.amorcage or self.silencieux:
            return None
        if not (self.cfg["notifications_telephone"] or self.cfg["notifications_windows"]):
            return None
        maintenant = time.time()
        if maintenant - item["ts_pub"] > self.cfg["age_max_push_minutes"] * 60:
            return None
        if c.get("amorcage") and item["niveau"] != "rouge":
            return None  # info déjà connue au lancement du radar : pas d'alerte, sauf si elle devient urgente
        if c["niveau"] == "rouge":
            if c.get("pousse") != "rouge":
                return "rouge"
            if c["etiquette"] == "confirme" and c.get("pousse_etiquette") != "confirme":
                return "confirmation"
            return None
        if c["niveau"] == "orange" and self.cfg["pousser_orange"] and not c.get("pousse"):
            if item["fiab"] in self.cfg["orange_fiabilites"] or c["etiquette"] == "confirme":
                derniers = [t for t, k in self.pousses if k == "orange" and maintenant - t < 3600]
                if len(derniers) < self.cfg["orange_max_par_heure"]:
                    self.pousses.append((maintenant, "orange"))
                    return "orange"
        return None

    # ------------------------------------------------------------ sources spéciales

    def traiter_tzeva(self, s: dict, data) -> None:
        maintenant = time.time()
        alertes = data if isinstance(data, list) else (data.get("alerts") or data.get("data") or []) if isinstance(data, dict) else []
        for a in alertes:
            if not isinstance(a, dict) or a.get("isDrill"):
                continue
            nid = str(a.get("notificationId") or a.get("id") or empreinte(json.dumps(a, sort_keys=True)))
            if nid in self.tz_vus:
                continue
            self.tz_vus[nid] = maintenant
            villes = [str(v) for v in (a.get("cities") or a.get("data") or []) if v]
            if self.salve is None or maintenant - self.salve["dernier"] > 300:
                self.clore_salve()
                self.salve = {"debut": maintenant, "dernier": maintenant, "villes": set(), "menaces": set(), "pousse": False}
            self.salve["dernier"] = maintenant
            self.salve["villes"].update(villes)
            self.salve["menaces"].add(a.get("threat"))
        self.tz_vus = {k: v for k, v in self.tz_vus.items() if maintenant - v < 86400}
        if self.salve and not self.salve["pousse"]:
            villes = self.salve["villes"]
            grandes = [n for n, motif in (("Tel-Aviv", "תל אביב"), ("Jérusalem", "ירושלים"), ("Haïfa", "חיפה"), ("Beer-Sheva", "באר שבע")) if any(motif in v for v in villes)]
            centre = any(g in ("Tel-Aviv", "Jérusalem") for g in grandes)
            if len(villes) >= self.cfg["tzevaadom_seuil_localites"] or centre:
                self.salve["pousse"] = True
                self.emettre_salve(s, rouge=True, grandes=grandes)

    def _libelle_menace(self) -> str:
        m = self.salve["menaces"] if self.salve else set()
        if m == {5}:
            return "drones / aéronefs hostiles"
        if m <= {0, None}:
            return "roquettes / missiles"
        return "roquettes, missiles ou drones"

    def emettre_salve(self, s: dict, rouge: bool, grandes=None) -> None:
        nb = len(self.salve["villes"])
        quoi = self._libelle_menace()
        if rouge:
            titre = (f"Sirènes en Israël : alerte {quoi} sur {nb} localités"
                     + (f", dont {', '.join(grandes)}" if grandes else "")
                     + " — possible tir de grande ampleur (Iran, Yémen ou Liban)")
        else:
            titre = f"Alerte {quoi} en Israël : {nb} localité(s) (sirènes, alerte locale)"
        lien = f"https://www.tzevaadom.co.il/en/?ref={int(self.salve['debut'])}"
        self.traiter(s, titre, lien, "", self.salve["debut"], s["editeur"], "O",
                     niveau_force="rouge" if rouge else "bleu",
                     categorie_force="Missiles sur Israël" if rouge else "Alerte locale Israël")

    def clore_salve(self) -> None:
        if self.salve and not self.salve["pousse"] and self.salve["villes"]:
            s = self.src_par_id.get("tzevaadom")
            if s:
                self.emettre_salve(s, rouge=False)
        self.salve = None

    def traiter_page(self, s: dict, contenu: str) -> None:
        txt = texte_brut(contenu)
        dates = sorted(set(re.findall(r"Date de mise (?:en ligne|à jour) le\s*:\s*\d{1,2}(?:er)?\s+\w+\s+\d{4}", txt)))
        if not dates:
            raise ValueError("repères de date introuvables sur la page")
        sig = empreinte("|".join(dates))
        ancien = self.pages.get(s["id"])
        self.pages[s["id"]] = {"sig": sig, "dates": dates, "vu": time.time()}
        if ancien and ancien.get("sig") != sig and not self.essai:
            nouvelles = [d.split(":", 1)[-1].strip() for d in dates if d not in ancien.get("dates", [])]
            titre = (f"France Diplomatie met à jour ses conseils aux voyageurs — {s.get('pays', '')}"
                     + (f" (nouvelle mention du {', '.join(nouvelles)[:80]})" if nouvelles else ""))
            self.traiter(s, titre, s["url"], "", time.time(), s["editeur"], "O",
                         niveau_force="orange", categorie_force="Conseils aux voyageurs")
        self.modifie = True

    # ------------------------------------------------------------ envois

    def synchro_ntfy(self, force: bool = False) -> None:
        """Lit les alertes déjà envoyées sur le canal (12 h) pour ne pas doubler le relais internet."""
        if self.essai or not self.cfg["notifications_telephone"] or not self.cfg["ntfy_sujet"]:
            return
        if not force and time.time() - self.hist_ntfy_maj < 600:
            return
        self.hist_ntfy_maj = time.time()
        try:
            url = f"{self.cfg['ntfy_serveur'].rstrip('/')}/{self.cfg['ntfy_sujet']}/json?poll=1&since=12h"
            _, data, _ = telecharger(url, timeout=15, ua=UA_RADAR)
            hist = []
            for ligne in data.decode("utf-8", "replace").splitlines():
                try:
                    m = json.loads(ligne)
                except ValueError:
                    continue
                if m.get("event") == "message":
                    hist.append({"click": m.get("click", ""), "jetons": jetons((m.get("message") or "").split("\n")[0])})
            self.hist_ntfy = hist
        except Exception as ex:
            log.info("Historique ntfy indisponible (%s)", ex)

    def deja_envoye(self, c: dict) -> bool:
        candidats = [set(jetons(c["titre"]))]
        if c.get("titre_fr"):
            candidats.append(set(jetons(c["titre_fr"])))
        for h in self.hist_ntfy:
            if c.get("lien") and h["click"] == c["lien"]:
                return True
            for j in candidats:
                if j and h["jetons"] and len(j & h["jetons"]) / len(j | h["jetons"]) >= 0.6:
                    return True
        return False

    def vider_file_push(self) -> None:
        if not self.file_push:
            return
        file, self.file_push = self.file_push, []
        vus, actions = set(), []
        for action, cid in file:
            if (action, cid) not in vus and cid in self.clusters:
                vus.add((action, cid))
                actions.append((action, self.clusters[cid]))
        ordre = {"rouge": 0, "confirmation": 1, "orange": 2}
        actions.sort(key=lambda x: ordre[x[0]])
        maxi = self.cfg["max_push_par_passage"]
        a_envoyer, reste = actions[:maxi], actions[maxi:]
        self.synchro_ntfy()
        for action, c in a_envoyer:
            if action == "confirmation" and c.get("pousse_etiquette") == "confirme":
                continue  # l'alerte partie juste avant portait déjà « Confirmé »
            etiquette_avant = c.get("pousse_etiquette")
            c["pousse_etiquette"] = c.get("etiquette")
            if not c.get("titre_fr"):
                fr = self.trad.traduire(c["titre"])
                if fr:
                    c["titre_fr"] = fr
            if action != "confirmation" and self.deja_envoye(c):
                continue  # déjà envoyée (par le relais internet pendant que le PC était éteint, par exemple)
            if action == "confirmation" and etiquette_avant is None:
                continue
            eds =", ".join(list(c["editeurs"])[:4]) + (" …" if len(c["editeurs"]) > 4 else "")
            if action == "confirmation":
                titre = f"✅ Confirmé · {c['categorie']}"
                prio = self.cfg["priorite"]["confirmation"]
            else:
                titre = f"{EMOJI[action]} {c['categorie']} · {ETIQUETTES[c['etiquette']]}"
                prio = self.cfg["priorite"][action]
            message = f"{c.get('titre_fr') or c['titre']}\n{eds} · {heure_paris(time.time())}"
            self.envoyer(titre, message, prio, c.get("lien", ""))
            self.hist_ntfy.append({"click": c.get("lien", ""), "jetons": jetons(c.get("titre_fr") or c["titre"])})
        if reste:
            self.envoyer(f"🔔 {len(reste)} autre(s) alerte(s)",
                         "Plusieurs infos importantes en même temps : ouvre le tableau de bord pour tout voir.\n"
                         + "\n".join("• " + (c.get("titre_fr") or c["titre"])[:90] for _, c in reste[:5]),
                         self.cfg["priorite"]["resume"], "")

    def envoyer(self, titre: str, message: str, priorite: int, lien: str) -> None:
        self.stats["push"].append(f"{titre} | {message.splitlines()[0]}")
        if self.essai:
            return
        log.info("ALERTE %s | %s", titre, message.replace("\n", " | "))
        if self.cfg["notifications_telephone"] and self.cfg["ntfy_sujet"]:
            try:
                envoyer_ntfy(self.cfg, titre, message, priorite, lien)
            except Exception as ex:
                log.warning("Envoi ntfy impossible : %s", ex)
        if self.cfg["notifications_windows"] and self.mode != "une_fois":
            notification_windows(titre, message, lien)

    # ------------------------------------------------------------ journal, état, tableau

    def journaliser(self, c: dict, action, nouveau: bool) -> None:
        ts = time.time()
        legende = ("🔴 urgent · 🟠 important · 🔵 info — ✅ confirmé · ⚠️ une seule source ou non vérifié · "
                   "🏛️ officiel / média d'État — 📲 = alerte envoyée sur le téléphone.\n\n")
        if self.amorcage:
            p = ALERTES / "etat-initial-72h.md"
            if not p.exists():
                p.write_text("# État initial : les 72 heures avant le lancement du radar\n\n"
                             "Heure de publication (Paris). " + legende, encoding="utf-8")
            ts = c.get("ts_pub") or ts
        else:
            p = ALERTES / f"{jour_paris(ts)}.md"
            if not p.exists():
                p.write_text(f"# Journal du {jour_long(ts)}\n\nTout ce que le radar a détecté, heure de détection (Paris). "
                             + legende, encoding="utf-8")
        titre = (c.get("titre_fr") or c["titre"]).replace("[", "(").replace("]", ")")
        vo = c["titre"] if c.get("titre_fr") and c["titre_fr"] != c["titre"] else ""
        lien = f"[{titre}]({c['lien']})" if c.get("lien") else titre
        eds = ", ".join(c["editeurs"])
        vo_txt = f" · *VO : {vo[:160]}*" if vo else ""
        if action == "confirmation":
            ligne = f"- **{heure_paris(ts)}** ✅ Désormais confirmé ({eds}) : {lien}{vo_txt}\n"
        else:
            ligne = (f"- **{heure_paris(ts)}** {EMOJI[c['niveau']]} {ETIQUETTES[c['etiquette']]} · *{c['categorie']}* — "
                     f"{lien} — {eds}{' 📲' if action else ''}{vo_txt}\n")
        with p.open("a", encoding="utf-8") as f:
            f.write(ligne)

    def sauvegarder(self) -> None:
        if self.essai:
            return
        maintenant = time.time()
        self.vus = {k: v for k, v in self.vus.items() if maintenant - v < 8 * 86400}
        self.clusters = {k: v for k, v in self.clusters.items() if maintenant - v["dernier"] < 72 * 3600}
        ecrire_json(ETAT / "vus.json", self.vus)
        ecrire_json(ETAT / "clusters.json", self.clusters)
        ecrire_json(ETAT / "pages.json", self.pages)
        self.trad.sauver()
        ecrire_json(ETAT / "sante.json", {"derniere_boucle": maintenant, "demarre": self.demarre,
                                          "mode": self.mode, "amorcage": self.amorcage, "sources": self.sante})

    def tableau(self) -> None:
        if self.essai:
            return
        maintenant = time.time()
        quand = lambda c: min(c.get("ts_pub") or c["premier"], c["premier"])
        cl = sorted(self.clusters.values(), key=quand, reverse=True)[:500]
        donnees = {
            "genere": maintenant, "heure": heure_paris(maintenant),
            "sources_total": len(self.sources),
            "sources_ok": sum(1 for s in self.sources if self.sante.get(s["id"], {}).get("ok") and not self.sante[s["id"]].get("err")),
            "clusters": [{
                "niveau": c["niveau"], "etiquette": ETIQUETTES[c.get("etiquette", "une_source")],
                "categorie": c["categorie"], "titre": c.get("titre_fr") or c["titre"],
                "vo": c["titre"] if c.get("titre_fr") and c["titre_fr"] != c["titre"] else "",
                "lien": c.get("lien", ""),
                "heure": heure_paris(quand(c)), "jour": jour_long(quand(c)).capitalize(),
                "liens": [[ed, l] for ed, l in c.get("liens", {}).items()] or [[ed, ""] for ed in c["editeurs"]],
                "pousse": bool(c.get("pousse")),
                "recherche": normaliser(c["titre"] + " " + (c.get("titre_fr") or "") + " " + " ".join(c["editeurs"]) + " " + c["categorie"]),
            } for c in cl],
        }
        js = json.dumps(donnees, ensure_ascii=False).replace("</", "<\\/")
        tmp = TABLEAU.with_suffix(".tmp")
        tmp.write_text(MODELE_TABLEAU.replace("__DONNEES__", js), encoding="utf-8")
        os.replace(tmp, TABLEAU)
        self.dernier_tableau = maintenant

    # ------------------------------------------------------------ boucle

    def pouls_github(self) -> None:
        """Toutes les 10 min, signale au relais internet que le PC est allumé (variable PC_POULS du dépôt).
        Tant que ce signal est frais, le relais ne fait que mettre son état à jour, sans envoyer d'alerte."""
        depot = self.cfg.get("relais_depot")
        if self.mode != "continu" or not depot or time.time() - self.dernier_pouls < 600:
            return
        self.dernier_pouls = time.time()
        gh = trouver_gh()
        if not gh:
            return

        def envoyer():
            try:
                p = subprocess.run([gh, "variable", "set", "PC_POULS", "--repo", depot, "--body", str(int(time.time()))],
                                   capture_output=True, text=True, timeout=60,
                                   creationflags=0x08000000 if os.name == "nt" else 0)
                if p.returncode != 0:
                    log.warning("Signal au relais internet impossible : %s", (p.stderr or p.stdout).strip()[:200])
            except Exception as ex:
                log.warning("Signal au relais internet impossible : %s", ex)

        self.pool.submit(envoyer)

    def tour(self) -> None:
        maintenant = time.time()
        for s in self.sources:
            sid = s["id"]
            if sid in self.en_cours or maintenant < self.prochain[sid]:
                continue
            self.en_cours[sid] = self.pool.submit(self.recuperer, s)
        for sid in [k for k, f in self.en_cours.items() if f.done()]:
            f = self.en_cours.pop(sid)
            s = self.src_par_id[sid]
            self.tentes.add(sid)
            try:
                res = f.result()
                self.integrer(s, res)
                self.erreurs[sid] = 0
                self.prochain[sid] = time.time() + s["intervalle"] * random.uniform(0.9, 1.1)
                st = self.sante.setdefault(sid, {})
                st.update(ok=time.time(), err=None, nom=s["nom"])
            except Exception as ex:
                self.erreurs[sid] += 1
                n = self.erreurs[sid]
                self.prochain[sid] = time.time() + min(s["intervalle"] * (2 ** min(n, 8)), 3600)
                st = self.sante.setdefault(sid, {})
                st.update(err=f"{type(ex).__name__}: {str(ex)[:160]}", err_ts=time.time(), nom=s["nom"])
                if n in (1, 5, 20) or n % 100 == 0:
                    log.warning("Source %s en erreur (%d fois) : %s", sid, n, st["err"])
        if self.salve and time.time() - self.salve["dernier"] > 300:
            self.clore_salve()
        self.vider_file_push()
        if self.amorcage and len(self.tentes) >= len(self.sources):
            self.amorcage = False
            log.info("Amorçage terminé : %d infos de départ enregistrées, les alertes sont actives.", len(self.clusters))
            self.modifie = True

    def boucle(self) -> None:
        log.info("Radar démarré : %d sources, amorçage=%s", len(self.sources), self.amorcage)
        self.synchro_ntfy(force=True)
        dernier_save = 0.0
        while True:
            try:
                self.tour()
                self.pouls_github()
                maintenant = time.time()
                if self.trad.actif and not self.amorcage and maintenant - self.derniere_retraduction > 600 \
                        and (self.retraduction is None or self.retraduction.done()):
                    self.derniere_retraduction = maintenant
                    self.retraduction = self.pool.submit(self.retraduire)
                if (self.modifie and maintenant - dernier_save > 20) or maintenant - dernier_save > 300:
                    self.sauvegarder()
                    self.tableau()
                    dernier_save = maintenant
                    self.modifie = False
            except Exception:
                log.exception("Erreur dans la boucle (le radar continue)")
            time.sleep(2)

    def un_passage(self, delai_max: float = 120) -> None:
        if not self.essai:
            self.synchro_ntfy(force=True)
        for s in self.sources:
            self.prochain[s["id"]] = 0
        debut = time.time()
        while time.time() - debut < delai_max:
            self.tour()
            if len(self.tentes) >= len(self.sources) and not self.en_cours:
                break
            time.sleep(0.5)
        self.vider_file_push()
        self.sauvegarder()
        self.tableau()


# --------------------------------------------------------------------------- commandes

def verrou_unique():
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    try:
        sock.bind(("127.0.0.1", PORT_VERROU))
        sock.listen(1)
        return sock
    except OSError:
        return None


def commande_depuis(minutes: float) -> None:
    limite = time.time() - minutes * 60
    clusters = lire_json(ETAT / "clusters.json", {})

    def retenu(c: dict) -> bool:
        if c["dernier"] < limite:
            return False
        if c.get("amorcage"):  # info de l'état initial : seulement si elle a vraiment bougé depuis
            return c["dernier"] - c["premier"] > 120
        return True

    choisis = [c for c in clusters.values() if retenu(c)]
    choisis.sort(key=lambda c: (-RANG[c["niveau"]], -c["premier"]))
    sante = lire_json(ETAT / "sante.json", {})
    der = sante.get("derniere_boucle")
    print(f"Radar : dernière boucle {heure_paris(der) if der else 'inconnue'} (heure de Paris)"
          + (" — ATTENTION radar arrêté depuis plus de 10 min" if der and time.time() - der > 600 else ""))
    print(f"{len(choisis)} info(s) détectée(s) ou mise(s) à jour ces {int(minutes)} dernières minutes "
          f"(🔴 et 🟠 en détail, 🔵 en résumé) :\n")
    nb_bleu = 0
    for c in choisis:
        sources = "; ".join(f"{ed} ({fi})" for ed, fi in c["editeurs"].items())
        if c["niveau"] == "bleu":
            nb_bleu += 1
            if nb_bleu <= 60:
                print(f"[🔵 {ETIQUETTES[c.get('etiquette', 'une_source')]}] {c.get('titre_fr') or c['titre']} — {sources}")
            continue
        print(f"[{EMOJI[c['niveau']]} {ETIQUETTES[c.get('etiquette', 'une_source')]} · {c['categorie']}] "
              f"publié {heure_paris(min(c.get('ts_pub') or c['premier'], c['premier']))}, vu {heure_paris(c['premier'])} — "
              f"{c.get('titre_fr') or c['titre']}")
        if c.get("titre_fr") and c["titre_fr"] != c["titre"]:
            print(f"    VO : {c['titre']}")
        print(f"    sources : {sources}")
        liens = sorted(c.get("liens", {}).items(), key=lambda x: len(x[1]))[:2]  # liens directs (courts) d'abord
        for ed, l in liens:
            print(f"    {ed} : {l}")
        if c.get("pousse"):
            print("    📲 alerte envoyée")
    if nb_bleu > 60:
        print(f"… et {nb_bleu - 60} autres infos 🔵 (voir tableau-de-bord.html)")


def commande_etat() -> None:
    sante = lire_json(ETAT / "sante.json", {})
    der = sante.get("derniere_boucle")
    print("Dernière boucle :", heure_paris(der) if der else "jamais", "| mode :", sante.get("mode"))
    ko = {k: v for k, v in sante.get("sources", {}).items() if v.get("err")}
    print(f"Sources en erreur : {len(ko)}")
    for k, v in ko.items():
        print(f"  - {k} ({v.get('nom')}) : {v.get('err')}")


def main() -> None:
    ap = argparse.ArgumentParser(description="Radar Veille US-Iran")
    ap.add_argument("--essai", action="store_true")
    ap.add_argument("--une-fois", action="store_true")
    ap.add_argument("--test-notif", action="store_true")
    ap.add_argument("--depuis", type=float)
    ap.add_argument("--etat", action="store_true")
    a = ap.parse_args()

    if sys.stdout and hasattr(sys.stdout, "reconfigure"):
        try:
            sys.stdout.reconfigure(encoding="utf-8")
        except Exception:
            pass

    if a.depuis is not None:
        commande_depuis(a.depuis)
        return
    if a.etat:
        commande_etat()
        return

    configurer_journal(console=bool(sys.stdout) and (a.essai or a.une_fois or a.test_notif))
    if a.test_notif:
        cfg = charger_config()
        if os.environ.get("GITHUB_ACTIONS"):
            envoyer_ntfy(cfg, "✅ Relais internet : test", "Le relais GitHub fonctionne : quand ton PC est éteint, "
                         "c'est lui qui t'enverra les alertes.", 3)
        else:
            envoyer_ntfy(cfg, "✅ Veille US-Iran : test", "Si tu lis ceci, les alertes arrivent bien sur ton téléphone.", 3)
            notification_windows("✅ Veille US-Iran : test", "Les alertes s'afficheront aussi ici, sur le PC.")
        print("Notification de test envoyée" + ("" if os.environ.get("GITHUB_ACTIONS") else " sur le canal : " + cfg["ntfy_sujet"]))
        return
    if a.essai:
        r = Radar("essai")
        r.un_passage()
        st = r.stats
        print(f"\nInfos pertinentes : {st['items']}  (🔴 {st['rouge']} · 🟠 {st['orange']} · 🔵 {st['bleu']})")
        print(f"Alertes qui seraient envoyées maintenant : {len(st['push'])}")
        for p in st["push"]:
            print("  📲", p)
        for niv in ("rouge", "orange"):
            print(f"\n--- Exemples {EMOJI[niv]} ---")
            for it in [x for x in st.get("exemples", []) if x["niveau"] == niv][:25]:
                print(f"  {it['editeur']:<22} {it['categorie']:<20} {it['titre'][:110]}")
        ko = {k: v for k, v in r.sante.items() if v.get("err")}
        print(f"\nSources en erreur : {len(ko)}")
        for k, v in ko.items():
            print(f"  - {k} : {v['err']}")
        sys.stdout.flush()
        os._exit(0)
    if a.une_fois:
        r = Radar("une_fois")
        r.un_passage()
        logging.shutdown()
        if sys.stdout:
            sys.stdout.flush()
        os._exit(0)

    verrou = verrou_unique()
    if verrou is None:
        log.info("Le radar tourne déjà : cette copie s'arrête.")
        return
    Radar("continu").boucle()


if __name__ == "__main__":
    main()
