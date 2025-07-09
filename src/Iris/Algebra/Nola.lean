import Iris.BI
import Iris.Algebra.CMRA
import Iris.Algebra.OFE
import Iris.Algebra.UPred
import Iris.Algebra.IProp
import Iris.Instances.UPred.Instance
import Iris.Algebra.Agree

inductive cif_binsel where
| /- Conjunction -/ cifs_and
| /- Disjunction -/ cifs_or
| /- Implication -/ cifs_imp
| /- Separating conjunction -/ cifs_sep
| /- Magic wand -/ cifs_wand

inductive cif_unsel where
| /- Plainly -/ cifs_plain
| /- Persistently -/ cifs_pers
| /- Basic update -/ cifs_bupd
| /- Except-0 -/ cifs_except0

inductive cif (FF : Iris.GFunctors) [Iris.IsGFunctors FF] : Type (u + 1) where
| /- Universal quantifier -/ cifs_all (A : Type u) (Φ : A -> cif FF)
| /- Existential quantifier -/ cifs_ex (A : Type u) (Φ : A -> cif FF)
| /- Binary operator -/ cifs_bin (s : cif_binsel) (P Q : cif FF)
| /- Unary operator -/ cifs_un (s : cif_unsel) (P : cif FF)
| /- Pure proposition -/ cifs_pure (P : Prop)
| /- Later -/ cifs_later (iP : Iris.IProp FF)
| /- Invariant -/ cifs_inv (fml : cif FF)
| /- Custom selector -/ cifs_own (M : Iris.COFE.OFunctorPre)
    (γ : Iris.GId FF) {Hlookup : FF[γ] = M} (m : Iris.COFE.OFunctor M)

section noliris
variable (FF : Iris.GFunctors) [Iris.IsGFunctors FF]

open Iris.BI

def cif_sem {FF} [Iris.IsGFunctors FF] (s : cif FF) : Iris.IProp FF :=
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
  | .cifs_inv _ => by sorry
  | @cif.cifs_own _ _ M γ Hlookup m => by /- apply (UPred.ownM m) -/ sorry

instance cif_inhabited : Inhabited (cif FF) where
  default := cif.cifs_pure True

notation "⟦" f "⟧" => cif_sem f

end noliris
