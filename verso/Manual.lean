import VersoManual

import Manual.Front

open Verso.Genre.Manual Verso.Output.Html

def extraHead : Array Verso.Output.Html := #[
  {{<link rel="icon" type="image/x-icon" href="static/favicon.svg"/>}},
  {{<link rel="stylesheet" href="static/style.css"/>}},
  {{<script src="static/scripts.js"></script>}},
]

def config : Config := {
  extraHead := extraHead,
  sourceLink := some "https://github.com/RemyDegenne/brownian-motion",
  issueLink := some "https://github.com/RemyDegenne/brownian-motion/issues",
}

def main := manualMain (%doc Manual.Front) (config := config)
