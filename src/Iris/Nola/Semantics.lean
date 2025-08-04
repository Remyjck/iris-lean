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

instance cif.inhabited : Inhabited (cif FF) where
  default := cif.pure True

syntax (name := sem) "⟦" (term:arg) "⟧" : term

macro_rules
  | `(⟦$f⟧)      => ``(cif.sem $f)

delab_rule cif.sem
  | `($_ $f) => ``(⟦$f⟧)

@[simp]
theorem cif.wandiff_sem (P Q : @cif.{u1} FF) :
  ⟦ cif(P ∗-∗ Q) ⟧ = iprop(⟦ P ⟧ ∗-∗ ⟦ Q ⟧) := by
  simp [cif.wandIff, cif.sem]

@[simp]
theorem cif.sem_lift (fP : cif FF) :
  ⟦(liftCif fP)⟧ ⊣⊢ ⟦ fP ⟧ := by
  induction fP with
  | all Φ ih =>
    simp_all [cif.sem, liftCif]
    constructor
    · iintro Hlift a; ispecialize Hlift (ULift.up a)
      istop; apply Iris.BI.entails_trans.trans Iris.BI.emp_sep.1
      apply (ih a).1
    · iintro HΦ a; ispecialize HΦ (a.down)
      istop; apply Iris.BI.entails_trans.trans Iris.BI.emp_sep.1
      apply (ih a.down).2
  | ex Φ ih =>
    simp_all [cif.sem, liftCif]
    constructor
    · iintro ⟨a, Hlift⟩; iexists (a.down)
      istop
      apply (ih a.down).1
    · iintro ⟨a, HΦ⟩; iexists (ULift.up a); istop
      apply (ih a).2
  | bin s P Q ihP ihQ =>
    simp_all [cif.sem, liftCif]
    cases s <;> simp []
    · apply Iris.BI.and_congr ihP ihQ
    · apply Iris.BI.or_congr ihP ihQ
    · apply Iris.BI.imp_congr ihP ihQ
    · apply Iris.BI.sep_congr ihP ihQ
    · apply Iris.BI.wand_congr ihP ihQ
  | un s P ih =>
    simp_all [cif.sem, liftCif]
    cases s <;> simp []
    · constructor <;> apply Iris.BIPlainly.mono
      apply ih.1; apply ih.2
    · apply persistently_congr ih
    · constructor <;> apply Iris.BIUpdate.mono
      apply ih.1; apply ih.2
    · unfold BIBase.except0; apply Iris.BI.or_congr_r ih
  | pure φ =>
    simp_all [cif.sem, liftCif]
  | later P =>
    simp_all [cif.sem, liftCif]
  | inv N F =>
    simp_all [cif.sem, liftCif]
    unfold inv_tok
    apply Iris.BI.exists_congr; intro i
    apply Iris.BI.sep_congr_r
    apply sinv_tok_lift
  | own a =>
    simp_all [cif.sem, liftCif]
