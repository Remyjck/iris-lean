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
| /- Custom selector -/ cifs_own (M : Iris.COFE.OFunctorPre)
  {Hlookup : ∃ (γ : Iris.GId FF), FF[γ] = M}

def cif_idom FF [Iris.IsGFunctors FF] (s : cif_sel FF) : Type :=
  match s with
  | .cifs_all A | .cifs_ex A => A
  | .cifs_bin _ => Bool
  | .cifs_un _ => Unit
  | .cifs_pure => Empty
  | .cifs_later => Empty
  | .cifs_inv fml => cif_idom FF fml
  | .cifs_own _ => Empty

def cif_data FF [Iris.IsGFunctors FF] (s : cif_sel FF) : Type _ :=
  match s with
  | .cifs_pure => Prop
  | .cifs_later => (Iris.IProp FF)
  | .cifs_own (M : Iris.COFE.OFunctorPre.{_}) => @Iris.COFE.OFunctor.{_} M
  | _ => Unit

section noliris
variable (FF : Iris.GFunctors) [Iris.IsGFunctors FF]

open Iris.BI

def cif_bsem {FF} [Iris.IsGFunctors FF] s :
  (cif_idom FF s -> Iris.IProp FF) -> (cif_data FF s) -> Iris.IProp FF :=
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
  | .cifs_later => λ _ Φ => iprop(▷ Φ)
  | .cifs_inv _ => λ _ => by sorry
  | @cif_sel.cifs_own _ _ M Hlookup => λ _ m => /- UPred.ownM m -/ by
    apply (@UPred.ownM (Iris.IResUR FF) _); simp [Iris.IResUR]
    sorry

section citg

structure citg (SEL : Type _) (I : SEL -> Type) (D : SEL -> Type) : Type _ where Citg ::
  citg_sel : SEL
  citg_ikids : I citg_sel -> citg SEL I D
  citg_data : D citg_sel

end citg

abbrev nullary {A} := @Empty.elim A
abbrev unary {A} (a : A) := λ () => a
abbrev binary {A} (a a' : A) := λ (b : Bool) => if b then a else a'

def cif FF [Iris.IsGFunctors FF] : Type _ :=
  citg (cif_sel FF) (cif_idom FF) (cif_data FF)

def cif_all {A} (Φx : A -> cif FF) : cif FF :=
  citg.Citg (cif_sel.cifs_all A) Φx ()
def cif_ex {A} (Φx : A -> cif FF) : cif FF :=
  citg.Citg (cif_sel.cifs_ex A) Φx ()

def cif_bin (s : cif_binsel) (Px Qx : cif FF) : cif FF :=
  citg.Citg (cif_sel.cifs_bin s) (binary Px Qx) ()
def cif_and :=
  cif_bin FF cif_binsel.cifs_and
def cif_or :=
  cif_bin FF cif_binsel.cifs_or
def cif_imp :=
  cif_bin FF cif_binsel.cifs_imp
def cif_sep :=
  cif_bin FF cif_binsel.cifs_sep
def cif_wand :=
  cif_bin FF cif_binsel.cifs_wand

def cif_un (s : cif_unsel) (Px : cif FF) : cif FF :=
  citg.Citg (cif_sel.cifs_un s) (unary Px) ()
def cif_plain : cif FF -> cif FF :=
  cif_un FF cif_unsel.cifs_plain
def cif_pers : cif FF -> cif FF :=
  cif_un FF cif_unsel.cifs_pers
def cif_bupd : cif FF -> cif FF :=
  cif_un FF cif_unsel.cifs_bupd
def cif_except0 : cif FF -> cif FF :=
  cif_un FF cif_unsel.cifs_except0

def cif_pure {FF} [Iris.IsGFunctors FF] (φ : Prop) : cif FF :=
  citg.Citg (cif_sel.cifs_pure) nullary φ
def cif_later (P : Iris.IProp FF) : cif FF :=
  citg.Citg (cif_sel.cifs_later) nullary P
def cif_inv (P : cif FF) : cif FF :=
  citg.Citg (cif_sel.cifs_inv P.citg_sel) P.citg_ikids ()
def cif_own {M : Iris.COFE.OFunctorPre} (m : Iris.COFE.OFunctor M) : cif FF :=
  citg.Citg (cif_sel.cifs_own M) nullary m

instance cif_inhabited : Inhabited (cif FF) where
  default := cif_pure True

def cif_sem {FF} [Iris.IsGFunctors FF] : cif FF -> Iris.IProp FF := λ s =>
  match s with
  | citg.Citg csel ckids cdata =>
    cif_bsem csel (λ i => cif_sem (ckids i)) cdata

notation "⟦" f "⟧" => cif_sem f

end noliris
