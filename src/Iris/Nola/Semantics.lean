import Iris.BI
import Iris.Algebra.CMRA
import Iris.Algebra.OFE
import Iris.Algebra.UPred
import Iris.Algebra.IProp
import Iris.Instances.UPred.Instance
import Iris.Algebra.Own
import Iris.ProofMode

import Iris.Nola.Syntax
import Iris.Nola.Notations
import Iris.Nola.Inv

section noliris
variable (FF : Iris.GFunctors)

open Iris.BI

def cif.sem {FF} (s : cif FF) : Iris.IProp FF :=
  match s with
  | @cif.all _ A Φ => iprop(∀ (a : A), cif.sem (Φ a))
  | @cif.ex _ A Φ => iprop(∃ (a : A), cif.sem (Φ a))
  | .bin s P Q => let (P, Q) := (cif.sem P, cif.sem Q);
    (match s with
    | .and => iprop(P ∧ Q) | .or => iprop(P ∨ Q)
    | .imp => iprop(P -> Q) | .wand => iprop(P -∗ Q)
    | .sep => iprop(P ∗ Q))
  | .un s P => let P := cif.sem P;
    (match s with
    | .plain => iprop(■ P) | .pers => iprop(<pers> P)
    | .bupd => iprop(|==> P)
    | .except0 => iprop(◇ P))
  | .pure φ => iprop(⌜φ⌝)
  | .later Φ => iprop(▷ Φ)
  | .inv N F => inv_tok N F
  | cif.own a => Iris.own a

instance cif_inhabited : Inhabited (cif FF) where
  default := cif.pure True

syntax (name := sem) "⟦" (term:arg) "⟧" : term

macro_rules
  | `(⟦$f⟧)      => ``(cif.sem $f)

delab_rule cif.sem
  | `($_ $f) => ``(⟦$f⟧)

@[simp]
theorem cif_wandiff_sem (P Q : @cif.{u1} FF) :
  ⟦ cif(P ∗-∗ Q) ⟧ = iprop(⟦ P ⟧ ∗-∗ ⟦ Q ⟧) := by
  simp [cif.wandIff, cif.sem]
