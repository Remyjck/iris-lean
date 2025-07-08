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

inductive cif_sel (FF : Iris.GFunctors) [Iris.IsGFunctors FF] : Type (u + 1) where
| /- Universal quantifier -/ cifs_all (A : Type u)
| /- Existential quantifier -/ cifs_ex (A : Type u)
| /- Binary operator -/ cifs_bin (s : cif_binsel)
| /- Unary operator -/ cifs_un (s : cif_unsel)
| /- Pure proposition -/ cifs_pure
| /- Later -/ cifs_later
| /- Invariant -/ cifs_inv (fml : cif_sel FF)
| /- Custom selector -/ cifs_own {M : Iris.COFE.OFunctorPre}
  (Hlookup : ∃ (γ : Iris.GId FF), FF[γ] = M) (s : Iris.COFE.OFunctor M)

def cif_idom FF [Iris.IsGFunctors FF] (s : cif_sel FF) : Type :=
  match s with
  | .cifs_all A | .cifs_ex A => A
  | .cifs_bin _ => Bool
  | .cifs_un _ => Unit
  | .cifs_pure | .cifs_later => Empty
  | .cifs_inv fml => cif_idom FF fml
  | @cif_sel.cifs_own _ _ M _ _ => Iris.COFE.OFunctor M

def cif_cdom FF [Iris.IsGFunctors FF] (s : cif_sel FF) : Type :=
  match s with
  | .cifs_all _ | .cifs_ex _ | .cifs_bin _ | .cifs_un _ | .cifs_pure | .cifs_later =>
    Empty
  | .cifs_inv fml => cif_cdom FF fml
  | @cif_sel.cifs_own _ _ _ _ _ => Empty

section noliris
variable (FF : Iris.GFunctors) [Iris.IsGFunctors FF]

open Iris.BI

def cif_bsem s : (cif_idom FF s -> Iris.IProp FF) -> Iris.IProp FF :=
  match s with
  | .cifs_all A => λ Φ => iprop(∀ (a : A), Φ a)
  | .cifs_ex A => λ Φ => iprop(∃ (a : A), Φ a)
  | .cifs_bin s => λ Φ =>
    (match s with
    | .cifs_and => iprop(Φ true ∧ Φ false) | .cifs_or => iprop(Φ true ∨ Φ false)
    | .cifs_imp => iprop(Φ true -> Φ false) | .cifs_wand => iprop(Φ true -∗ Φ false)
    | .cifs_sep => iprop(Φ true ∗ Φ false))
  | .cifs_un s => λ Φ =>
    (match s with
    | .cifs_plain => iprop(■ Φ ()) | .cifs_pers => iprop(□ Φ ())
    | .cifs_bupd => iprop(|==> Φ ())
    | .cifs_except0 => iprop(◇ Φ ()))
  | .cifs_pure => λ _ => by sorry | .cifs_later => λ _ => by sorry
  | .cifs_inv _ => λ _ => by sorry
  | @cif_sel.cifs_own _ _ M ⟨ γ, Hlookup ⟩ m => λ _ => /- UPred.ownM m -/ by sorry

end noliris
