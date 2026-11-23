"""Link each Lean declaration of the blueprint to its checked source line.

`source-links.tsv` maps every fully qualified name to a GitHub URL at a pinned
revision: this repository's for its own modules, the provider's for proofs that
live in a pinned provider package. `blueprint/scripts/check.py --write` writes it.
"""
from pathlib import Path


def ProcessOptions(options, document):
    table = Path(__file__).with_name("source-links.tsv").read_text(encoding="utf-8")
    links = dict(line.split("\t") for line in table.splitlines())

    def set_source_links():
        for graph in document.userdata["dep_graph"]["graphs"].values():
            for node in graph.nodes:
                node.userdata["lean_urls"] = [(name, links[name]) for name in node.userdata.get("leandecls", [])]

    document.addPostParseCallbacks(160, set_source_links)
