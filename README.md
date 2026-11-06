# Relais Veille US-Iran

Ce dépôt sert de relais à un radar d'actualité personnel. Le radar suit la situation entre les États-Unis, l'Iran et Israël, et ses effets sur Dubaï et le Golfe.

- La tâche GitHub Actions `relais.yml` lance `radar/radar.py --une-fois` toutes les 5 minutes.
- Le radar lit des sources fiables : agences de presse, grands médias, sources officielles.
- Les alertes partent sur un canal ntfy privé. Son nom est stocké dans le secret `NTFY_SUJET`.
- Quand le PC principal est allumé, il le signale par la variable `PC_POULS`. Le relais se contente alors de mettre son état à jour, pour éviter les doublons.

Les fichiers du dossier `radar/` sont des copies. On les met à jour depuis le PC avec `mettre-a-jour-relais.cmd`.
