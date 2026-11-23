# Adapted from daviddhilbert/special-transformations (MIT), via the ACVF-QE and
# Fubini-theorems blueprints; see blueprint/README.md.
"""Render a clickable dependency graph for local file previews."""

from textwrap import fill

from plasTeX.PackageResource import PackagePreCleanupCB


def render_graph(document):
    graph = document.userdata["dep_graph"]["graphs"][document]
    dot = graph.to_dot(document.userdata["dep_graph"]["shapes"]).tred()
    dot.graph_attr.update(bgcolor="white", pad="0.2")
    dot.node_attr.update(fontname="sans-serif", fontsize="10")
    for node in graph.nodes:
        title = node.attributes["title"].textContent
        label = fill(f"{node.caption} {title}", width=30)
        dot.get_node(node.id).attr.update(label=label, URL=str(node.url))

    output = "dependency-graph.svg"
    dot.write("dependency-graph.dot")
    dot.draw(output, prog="dot")
    return [output, "dependency-graph.dot"]


def ProcessOptions(options, document):
    data = document.userdata["dep_graph"]
    data.setdefault("shapes", {"definition": "box"}).update(
        assumption="box", imported="box"
    )
    data["legend"].extend([
        ("Amber boxes", "explicit hypotheses of the Lean theorems"),
        ("Purple boxes", "results recalled from the Fubini paper and proved in its package"),
    ])
    color = data["colorizer"]
    fillcolor = data["fillcolorizer"]
    borders = {"assumption": "#8a5a12", "imported": "#4e3b9e"}
    fills = {"assumption": "#ffe8b3", "imported": "#e4e0ff"}
    data["colorizer"] = lambda node: borders.get(node.thmName) or color(node)
    data["fillcolorizer"] = lambda node: fills.get(node.thmName) or fillcolor(node)
    document.addPackageResource(PackagePreCleanupCB(data=render_graph))
