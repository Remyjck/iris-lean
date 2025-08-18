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

def Fml.sem {FF} (s : Fml FF) : Iris.IProp FF :=
  match s with
  | @Fml.all _ A Φ => iprop(∀ (a : A), Fml.sem (Φ a))
  | @Fml.ex _ A Φ => iprop(∃ (a : A), Fml.sem (Φ a))
  | .bin s P Q => let (P, Q) := (Fml.sem P, Fml.sem Q);
    (match s with
    | .and => iprop(P ∧ Q) | .or => iprop(P ∨ Q)
    | .imp => iprop(P -> Q) | .wand => iprop(P -∗ Q)
    | .sep => iprop(P ∗ Q))
  | .un s P => let P := Fml.sem P;
    (match s with
    | .plain => iprop(■ P) | .pers => iprop(<pers> P)
    | .bupd => iprop(|==> P)
    | .except0 => iprop(◇ P))
  | .pure φ => iprop(⌜φ⌝)
  | .later Φ => iprop(▷ Φ)
  | .inv N F => inv_tok N F
  | Fml.own a => Iris.own a


instance Fml.inhabited : Inhabited (Fml FF) where
  default := Fml.pure True

syntax (name := sem) "⟦" (term:arg) "⟧" : term

macro_rules
  | `(⟦$f⟧)      => ``(Fml.sem $f)

delab_rule Fml.sem
  | `($_ $f) => ``(⟦$f⟧)

noncomputable def Fml.sForall.{u} {FF} (Φ : Fml.{u} FF → Prop) : Fml.{u} FF :=
  fml(∀ (p : ULift (Iris.IProp FF)),
      let fp : Fml.{u} FF := Classical.epsilon (fun fp => (⊢ iprop(⟦ (fp) ⟧ ∗-∗ p.down)) ∧ Φ fp)
      fml(⌜(⊢ ⟦ fp ⟧ ∗-∗ p.down) ∧ Φ fp⌝ -> fp))

noncomputable def Fml.sExists.{u} {FF} (Φ : Fml.{u} FF → Prop) : Fml.{u} FF :=
  fml(∃ (p : ULift (Iris.IProp FF)),
      let fp : Fml.{u} FF := Classical.epsilon (fun fp => (⊢ iprop(⟦ (fp) ⟧ ∗-∗ p.down)) ∧ Φ fp)
      fml(⌜(⊢ ⟦ fp ⟧ ∗-∗ p.down) ∧ Φ fp⌝ ∧ fp))

@[simp]
theorem sem_sForall (Φ : Fml FF -> Prop) :
  ⟦ (Fml.sForall.{u} Φ) ⟧ =
  iprop(∀ (p : ULift.{u, 0} (Iris.IProp FF)),
      let formula := Classical.epsilon fun fp => (⊢ ⟦fp⟧ ∗-∗ p.down) ∧ Φ fp
      iprop(⌜(⊢ ⟦formula⟧ ∗-∗ p.down) ∧ Φ formula⌝ → ⟦formula⟧)) := by
 simp [Fml.sForall, Fml.sem, Fml.imp]

@[simp]
theorem sem_sExists (Φ : Fml FF -> Prop) :
 ⟦ (Fml.sExists.{u} Φ) ⟧ =
 iprop(∃ (p : ULift.{u, 0} (Iris.IProp FF)),
      let formula := Classical.epsilon fun fp => (⊢ ⟦fp⟧ ∗-∗ p.down) ∧ Φ fp
      iprop(⌜(⊢ ⟦formula⟧ ∗-∗ p.down) ∧ Φ formula⌝ ∧ ⟦formula⟧)) := by
 simp [Fml.sExists, Fml.sem, Fml.and]

@[simp]
theorem Fml.wandiff_sem (P Q : @Fml.{u1} FF) :
  ⟦ fml(P ∗-∗ Q) ⟧ = iprop(⟦ P ⟧ ∗-∗ ⟦ Q ⟧) := by
  simp [Fml.wandIff, Fml.sem]

@[simp]
theorem sem_and (P Q : Fml FF) : ⟦fml(P ∧ Q)⟧ = iprop(⟦P⟧ ∧ ⟦Q⟧) := rfl
@[simp]
theorem sem_or (P Q : Fml FF) : ⟦fml(P ∨ Q)⟧ = iprop(⟦P⟧ ∨ ⟦Q⟧) := rfl
@[simp]
theorem sem_imp (P Q : Fml FF) : ⟦fml(P → Q)⟧ = iprop(⟦P⟧ → ⟦Q⟧) := rfl
@[simp]
theorem sem_sep (P Q : Fml FF) : ⟦fml(P ∗ Q)⟧ = iprop(⟦P⟧ ∗ ⟦Q⟧) := rfl
@[simp]
theorem sep_wand (P Q : Fml FF) : ⟦fml(P -∗ Q)⟧ = iprop(⟦P⟧ -∗ ⟦Q⟧) := rfl
@[simp]
theorem sep_persistently (P : Fml FF) : ⟦fml(<pers> P)⟧ = iprop(<pers> ⟦P⟧) := rfl

@[simp]
theorem Fml.sem_lift (fP : Fml FF) :
  ⟦(liftFml fP)⟧ ⊣⊢ ⟦ fP ⟧ := by
  induction fP with
  | all Φ ih =>
    simp_all [Fml.sem, liftFml]
    constructor
    · iintro Hlift a; ispecialize Hlift (ULift.up a)
      istop; apply Iris.BI.entails_trans.trans Iris.BI.emp_sep.1
      apply (ih a).1
    · iintro HΦ a; ispecialize HΦ (a.down)
      istop; apply Iris.BI.entails_trans.trans Iris.BI.emp_sep.1
      apply (ih a.down).2
  | ex Φ ih =>
    simp_all [Fml.sem, liftFml]
    constructor
    · iintro ⟨a, Hlift⟩; iexists (a.down)
      istop
      apply (ih a.down).1
    · iintro ⟨a, HΦ⟩; iexists (ULift.up a); istop
      apply (ih a).2
  | bin s P Q ihP ihQ =>
    simp_all [Fml.sem, liftFml]
    cases s <;> simp []
    · apply Iris.BI.and_congr ihP ihQ
    · apply Iris.BI.or_congr ihP ihQ
    · apply Iris.BI.imp_congr ihP ihQ
    · apply Iris.BI.sep_congr ihP ihQ
    · apply Iris.BI.wand_congr ihP ihQ
  | un s P ih =>
    simp_all [Fml.sem, liftFml]
    cases s <;> simp []
    · constructor <;> apply Iris.BIPlainly.mono
      apply ih.1; apply ih.2
    · apply persistently_congr ih
    · constructor <;> apply Iris.BIUpdate.mono
      apply ih.1; apply ih.2
    · unfold BIBase.except0; apply Iris.BI.or_congr_r ih
  | pure φ =>
    simp_all [Fml.sem, liftFml]
  | later P =>
    simp_all [Fml.sem, liftFml]
  | inv N F =>
    simp_all [Fml.sem, liftFml]
    unfold inv_tok
    apply Iris.BI.exists_congr; intro i
    apply Iris.BI.sep_congr_r
    apply sinv_tok_lift
  | own a =>
    simp_all [Fml.sem, liftFml]

-- noncomputable def sForall.{u} (Φ : Fml.{u} FF → Prop) : Fml.{u} FF :=
--   Classical.epsilon (fun p =>
--     ∃ (A : Type) (a : A) (P : A -> Fml.{u} FF), Φ p = (⊢ ⟦ (P a) ⟧))
