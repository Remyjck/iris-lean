/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Mario Carneiro
-/

import Iris.BI
import Iris.Algebra.OFE
import Iris.Algebra.CMRA
import Iris.Algebra.AProp

section aPropInstance

open Iris BI

variable (M : Type) [UCMRA M]

axiom equiv_entails : P ≡ Q -> aentails M P Q

instance bi_inst : BIBase (AProp M) where
  Entails      := @Iris.entails M _ (aentails M)
  emp          := Iris.emp M
  pure         := Iris.pure M
  and          := Iris.and M
  or           := Iris.or M
  imp          := Iris.imp M
  sForall      := Iris.sForall M
  sExists      := Iris.sExists M
  sep          := Iris.sep M
  wand         := Iris.wand M
  persistently := Iris.persistently M
  later        := Iris.later M

instance aProp_entails_preorder : Std.Preorder (Entails (PROP := AProp M)) where
  refl {x} := by simp [Entails]; unfold Iris.entails; apply aentails_refl
  trans {x y z} := by
    simp [Entails]; unfold Iris.entails
    intros Hxy Hyz; refine (aentails_trans M x.car y.car z.car Hxy Hyz)

instance later_contractive : OFE.Contractive (Iris.later M) (α := AProp M) where
  distLater_dist {n x y} Hl :=
    match n with
    | 0 => by apply later_dist_zero
    | n + 1 => by apply (later_dist_succ M _ _ Hl)

instance : BI (AProp M) where
  entails_preorder := inferInstance
  equiv_iff {P Q} := by
    constructor <;> intro HE
    · constructor <;> apply equiv_entails; apply HE
      · apply OFE.Equiv.symm; apply HE
    · simp [OFE.Equiv]; cases HE; sorry
  and_ne.ne n := by
    simp [OFE.Dist]
    intros x y Hxy x' y' Hxy'
    cases x; cases y; cases x'; cases y';
    simp_all only [BI.and, Iris.and];
    apply Iris.and_ne <;> assumption
  or_ne.ne n := by
    simp [OFE.Dist]
    intros x y Hxy x' y' Hxy'
    cases x; cases y; cases x'; cases y';
    simp_all only [BI.or, Iris.or];
    apply Iris.or_ne <;> assumption
  imp_ne.ne n := by
    simp [OFE.Dist]
    intros x y Hxy x' y' Hxy'
    cases x; cases y; cases x'; cases y';
    simp_all only [BI.imp, Iris.imp];
    apply Iris.imp_ne <;> assumption
  sep_ne.ne n := by
    simp [OFE.Dist]
    intros x y Hxy x' y' Hxy'
    cases x; cases y; cases x'; cases y';
    simp_all only [BI.sep, Iris.sep];
    apply Iris.sep_ne <;> assumption
  wand_ne.ne n := by
    simp [OFE.Dist]
    intros x y Hxy x' y' Hxy'
    cases x; cases y; cases x'; cases y';
    simp_all only [BI.wand, Iris.wand];
    apply Iris.wand_ne <;> assumption
  persistently_ne.ne n x y Hxy := by
    simp_all only [BI.persistently, Iris.persistently, OFE.Dist]
    apply (pers_ne M _ _ Hxy)
  later_ne := inferInstanceAs (OFE.NonExpansive (Iris.later M))
  sForall_ne {n x y} Hxy := by
    simp [sForall, OFE.Dist, Iris.sForall]
    unfold liftRel at Hxy; sorry
  sExists_ne {n x y} Hxy := by
    simp [sForall, OFE.Dist, Iris.sForall]
    unfold liftRel at Hxy; sorry
  pure_intro {p ap} Hp := by sorry
  pure_elim' {p ap} Hp := by sorry
  and_elim_l {p q} := by sorry
  and_elim_r {p q} := by sorry
  and_intro H1 H2 := by sorry
  or_intro_l {p q} := by sorry
  or_intro_r {p q} := by sorry
  or_elim {p q r} H1 H2 := by sorry
  imp_intro {p q r} I := by sorry
  imp_elim {p q r} I := by sorry
  sForall_intro {p f} H := by sorry
  sForall_elim {p f} H := by sorry
  sExists_intro {p f} H := by sorry
  sExists_elim {p f} H := by sorry
  sep_mono {p p' q q'} H1 H2 := by sorry
  emp_sep {P} := by
    constructor
    · simp [sep, emp, Iris.emp, Iris.sep]; sorry
    · simp [sep, emp, Iris.emp, Iris.sep]; sorry
  sep_symm {p q} := by sorry
  sep_assoc_l {p q r} := by sorry
  wand_intro {p q r} Hr := by sorry
  wand_elim {p q r} Hr := by sorry
  persistently_mono {p q} Hp := by sorry
  persistently_idem_2 {p} := by sorry
  persistently_emp_2 := by sorry
  persistently_and_2 {p q} := by sorry
  persistently_sExists_1 {f} := by sorry
  persistently_absorb_l {p q} := by sorry
  persistently_and_l {p q} := by sorry
  later_mono {p q} H := by sorry
  later_intro {p} := by sorry
  later_sForall_2 {Ψ} := by sorry
  later_sExists_false {Ψ} := by sorry
  later_sep {p q} := by sorry
  later_persistently {p q} := by sorry
  later_false_em {p} := by sorry

instance : BILaterContractive (AProp M) where
  toContractive := later_contractive M

instance (P : AProp M) : Affine P where
  affine := by simp [emp, Iris.emp]; apply pure_intro; constructor

theorem ownM_valid (m : M) : Iris.ownM M m ⊢ Iris.cmraValid M m := by
  sorry

theorem ownM_op (m1 m2 : M) : Iris.ownM M (m1 • m2) ⊣⊢ Iris.ownM M m1 ∗ Iris.ownM M m2 := by
  sorry

theorem ownM_always_invalid_elim (m : M) (H : ∀ n, ¬✓{n} m) : cmraValid M m ⊢ False := by
  sorry
