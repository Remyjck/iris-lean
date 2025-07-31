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

inductive cif.{u} (FF : Iris.GFunctors) : Type (u + 1) where
| /- Universal quantifier -/ all {A : Type u} (Φ : A -> cif FF)
| /- Existential quantifier -/ ex {A : Type u} (Φ : A -> cif FF)
| /- Binary operator -/ bin (s : cif.binsel) (P : cif FF) (Q : cif FF)
| /- Unary operator -/ un (s : cif.unsel) (P : cif FF)
| /- Pure proposition -/ pure (P : Prop)
| /- Later -/ later (iP : Iris.IProp FF)
| /- Invariant -/ inv (N : Namespace) (fml : cif FF)
| /- Custom selector -/ own [Iris.CMRA A] [inG FF A] (a : A)

namespace cif

def wandIff {FF} (P Q : cif FF) : cif FF :=
  cif.bin binsel.and
    (cif.bin binsel.wand P Q)
    (cif.bin binsel.wand Q P)

def plain (P : cif FF) : cif FF := cif.un unsel.plain P
def pers (P : cif FF) : cif FF := cif.un unsel.pers P
def bupd (P : cif FF) : cif FF := cif.un unsel.bupd P
def except0 (P : cif FF) : cif FF := cif.un unsel.except0 P

def and (P Q : cif FF) : cif FF := cif.bin binsel.and P Q
def or (P Q : cif FF) : cif FF := cif.bin binsel.or P Q
def imp (P Q : cif FF) : cif FF := cif.bin binsel.imp P Q
def sep (P Q : cif FF) : cif FF := cif.bin binsel.sep P Q
def wand (P Q : cif FF) : cif FF := cif.bin binsel.wand P Q

end cif
