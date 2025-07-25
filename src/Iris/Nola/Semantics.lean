import Iris.BI
import Iris.Algebra.CMRA
import Iris.Algebra.OFE
import Iris.Algebra.UPred
import Iris.Algebra.IProp
import Iris.Instances.UPred.Instance
import Iris.Algebra.Own
import Iris.ProofMode

import Iris.Nola.Syntax
import Iris.Nola.Inv

section noliris
variable (FF : Iris.GFunctors)

open Iris.BI

def cif_sem {FF} (s : cif FF) : Iris.IProp FF :=
  match s with
  | .cifs_all A Φ => iprop(∀ (a : A), cif_sem (Φ a))
  | .cifs_ex A Φ => iprop(∃ (a : A), cif_sem (Φ a))
  | .cifs_bin s P Q => let (P, Q) := (cif_sem P, cif_sem Q);
    (match s with
    | .cifs_and => iprop(P ∧ Q) | .cifs_or => iprop(P ∨ Q)
    | .cifs_imp => iprop(P -> Q) | .cifs_wand => iprop(P -∗ Q)
    | .cifs_sep => iprop(P ∗ Q))
  | .cifs_un s P => let P := cif_sem P;
    (match s with
    | .cifs_plain => iprop(■ P) | .cifs_pers => iprop(□ P)
    | .cifs_bupd => iprop(|==> P)
    | .cifs_except0 => iprop(◇ P))
  | .cifs_pure φ => iprop(⌜φ⌝)
  | .cifs_later Φ => iprop(▷ Φ)
  | .cifs_inv N F => inv_tok N F
  | cif.cifs_own a => own a

instance cif_inhabited : Inhabited (cif FF) where
  default := cif.cifs_pure True

notation "⟦" f "⟧" => cif_sem f

@[simp]
theorem cif_wandiff_sem (P Q : @cif.{u1} FF) :
  ⟦ cifs_wandiff P Q ⟧ = iprop(⟦ P ⟧ ∗-∗ ⟦ Q ⟧) := by
  simp [cifs_wandiff, cif_sem]
