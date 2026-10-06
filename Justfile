# Format and regenerate keys of references.bib
references:
    bibtool -F -r .bibtoolrsc -i ./references.bib -o references.bib
    sed -i '1{/^$/d}' references.bib

# Generate the import graph of GoodsteinPA as import_graph.{dot,png,pdf,html} (requires graphviz)
import-graph:
    lake exe graph --to GoodsteinPA import_graph.dot import_graph.png import_graph.pdf import_graph.html

mk-all:
    lake exe mk_all --module

shake:
    lake shake GoodsteinPA --keep-public --fix

# Axiom audit of every GoodsteinPA declaration against forgive.yml (run after `lake build`)
axiom-audit:
    lake exe forgive GoodsteinPA --json .lake/audit.json
