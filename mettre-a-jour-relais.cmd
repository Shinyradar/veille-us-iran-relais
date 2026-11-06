@echo off
rem Copie la version actuelle du radar (code, sources, regles) dans le relais internet et l'envoie sur GitHub.
cd /d "%~dp0"
if not exist radar mkdir radar
copy /y "..\radar\radar.py" "radar\radar.py" >nul
copy /y "..\radar\sources.json" "radar\sources.json" >nul
copy /y "..\radar\regles.json" "radar\regles.json" >nul
git add -A
git diff --cached --quiet && (echo Relais deja a jour.) || (git commit -m "Mise a jour du radar" && git push)
timeout /t 4 >nul
