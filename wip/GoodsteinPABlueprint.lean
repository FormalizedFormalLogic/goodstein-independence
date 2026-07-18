/-
Blueprint-only root.

This module makes the Path B audit declarations visible to leanblueprint/checkdecls without
importing them from the public `GoodsteinPA` root.
-/
import GoodsteinPA.OperatorZinfty
import GoodsteinPA.OperatorZeh
import GoodsteinPA.EwIter
import GoodsteinPA.OperatorZef2
import GoodsteinPA.WainerLadder
import GoodsteinPA.PathBProbe
-- SERIES-4 discharge: blueprint nodes 14 (`wainer_axiom`) / 15 (`routeB_headline`) moved here from
-- WainerRoute when the axiom became a theorem, so the audit must see them.
import GoodsteinPA.WainerBound
-- Foundation's finitary Gentzen Hauptsatz, imported solely so the blueprint's
-- `\lean{LO.FirstOrder.hauptsatz}` binding resolves (making thm:hauptsatz a real
-- green node — proved & kernel-clean upstream — rather than an orange gap).
import Foundation.FirstOrder.Hauptsatz
