import Iris.BI
import Iris.Algebra.Own
import Iris.Std.Namespaces

inductive cif.binsel where
| /- Conjunction -/ and
| /- Disjunction -/ or
| /- Implication -/ imp
| /- Separating conjunction -/ sep
| /- Magic wand -/ wand

inductive cif.unsel where
| /- Plainly -/ plain
| /- Persistently -/ pers
| /- Basic update -/ bupd
| /- Except-0 -/ except0

set_option pp.universes true

inductive cif.{u} (FF : Iris.GFunctors) : Type (u + 1) where
| all {A : Type u} (Φ : A → cif FF)
| ex  {A : Type u} (Φ : A → cif FF)
| bin (s : cif.binsel) (P : cif FF) (Q : cif FF)
| un  (s : cif.unsel) (P : cif FF)
| pure (P : Prop)
| later (iP : Iris.IProp FF)
| inv (N : Namespace) (fml : cif FF)
| own {A : Type} [Iris.CMRA A] [inG FF A] (a : A)

def liftCif.{u, v} (P : cif.{u} FF) : cif.{max u v} FF :=
  match P with
  | @cif.all _ A Φ =>
      -- We need to lift the domain type A from Type u to Type (max u v)
      cif.all (fun (a : ULift.{max u v, u} A) => liftCif (Φ a.down))
  | @cif.ex _ A Φ =>
      cif.ex (fun (a : ULift.{max u v, u} A) => liftCif (Φ a.down))
  | cif.bin s P Q =>
      cif.bin s (liftCif P) (liftCif Q)
  | cif.un s P =>
      cif.un s (liftCif P)
  | cif.pure P =>
      cif.pure P
  | cif.later iP =>
      cif.later iP
  | cif.inv N fml =>
      cif.inv N (liftCif fml)
  | cif.own a =>
      cif.own a

namespace cif

def wandIff {FF} (P Q : cif FF) : cif FF :=
  cif.bin binsel.and
    (cif.bin binsel.wand P Q)
    (cif.bin binsel.wand Q P)

def plain (P : cif FF) : cif FF := cif.un unsel.plain P
def pers (P : cif FF) : cif FF := cif.un unsel.pers P
def bupd (P : cif FF) : cif FF := cif.un unsel.bupd P
def except0 (P : cif FF) : cif FF := cif.un unsel.except0 P

def and.{u, v} (P : cif.{u} FF) (Q : cif.{v} FF) : cif.{max u v} FF :=
  bin cif.binsel.and (liftCif P) (liftCif Q)

def or (P Q : cif FF) : cif FF := cif.bin binsel.or P Q

def imp.{u, v} (P : cif.{u} FF) (Q : cif.{v} FF) : cif.{max u v} FF :=
  bin cif.binsel.imp (liftCif P) (liftCif Q)

def sep (P Q : cif FF) : cif FF := cif.bin binsel.sep P Q
def wand (P Q : cif FF) : cif FF := cif.bin binsel.wand P Q

def sForall.{u} (Φ : cif.{u} FF → Prop) : cif.{u + 1} FF :=
  all (fun (p : cif FF) => imp.{u + 1, u} (pure (Φ p)) p)
def sExists (Φ : cif.{u} FF → Prop) : cif.{u + 1} FF :=
  ex (fun p => and.{u + 1, u} (pure (Φ p)) p)

def all' {α} (P : α → cif FF) : cif FF := sForall (fun p => ∃ a, P a = p)
def ex' {α} (P : α → cif FF) : cif FF := sExists (fun p => ∃ a, P a = p)


end cif
