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
  | .cifs_pure => Empty
  | .cifs_later => Unit
  | .cifs_inv fml => cif_idom FF fml
  | .cifs_own _ _ => Empty

def cif_data FF [Iris.IsGFunctors FF] (s : cif_sel FF) : Type :=
  match s with
  | .cifs_pure => Prop
  | .cifs_later => (Iris.IProp FF)
  | _ => Empty

section noliris
variable (FF : Iris.GFunctors) [Iris.IsGFunctors FF]

open Iris.BI

def cif_bsem s : (cif_idom FF s -> Iris.IProp FF) -> (cif_data FF s) -> Iris.IProp FF :=
  match s with
  | .cifs_all A => λ Φ _ => iprop(∀ (a : A), Φ a)
  | .cifs_ex A => λ Φ _ => iprop(∃ (a : A), Φ a)
  | .cifs_bin s => λ Φ _ => let (P, Q) := (Φ true, Φ false);
    (match s with
    | .cifs_and => iprop(P ∧ Q) | .cifs_or => iprop(P ∨ Q)
    | .cifs_imp => iprop(P -> Q) | .cifs_wand => iprop(P -∗ Q)
    | .cifs_sep => iprop(P ∗ Q))
  | .cifs_un s => λ Φ _ => let P := Φ ();
    (match s with
    | .cifs_plain => iprop(■ P) | .cifs_pers => iprop(□ P)
    | .cifs_bupd => iprop(|==> P)
    | .cifs_except0 => iprop(◇ P))
  | .cifs_pure => λ _ φ => iprop(⌜φ⌝)
  | .cifs_later => λ Φ _ => iprop(▷ Φ ())
  | .cifs_inv _ => λ _ => by sorry
  | @cif_sel.cifs_own _ _ M Hlookup m => /- UPred.ownM m -/ by
    intros _ _
    apply (@UPred.ownM (Iris.IResUR FF) _); simp [Iris.IResUR]
    sorry


end noliris
