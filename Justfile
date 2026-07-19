# Format and regenerate keys of references.bib
format-bib:
    bibtool -F -r .bibtoolrsc -i ./references.bib -o references.bib
    sed -i '1{/^$/d}' references.bib

# Generate the import graph of GoodsteinPA as import_graph.{dot,png,pdf,html} (requires graphviz)
import-graph:
    lake exe graph --to GoodsteinPA import_graph.dot import_graph.png import_graph.pdf import_graph.html

mk-all:
    lake exe mk_all --module

shake:
    lake shake GoodsteinPA --keep-public --fix
