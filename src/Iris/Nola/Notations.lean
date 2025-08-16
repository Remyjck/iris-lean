import Iris.Nola.Syntax

open Lean

-- define `fml` embedding in `term`
syntax:max "fml(" term ")" : term
syntax:max "term(" term ")" : term

-- allow fallback to `term`
macro_rules
  | `(fml(term($t))) => pure t
  | `(fml($t))       => pure t

-- carry `fml` over some `term` constructs
macro_rules
  | `(fml(($P)))                  => ``((fml($P)))
  | `(fml(if $c then $t else $e)) => ``(if $c then fml($t) else fml($e))
  | `(fml(($P : $t)))             => ``((fml($P) : $t))

macro:max "fml(" P:term " : " t:term ")" : term => `((fml($P) : $t))

/-- Remove an `fml` quotation from a `term` syntax object. -/
partial def unpackCif [Monad m] [MonadRef m] [MonadQuotation m] : Term → m Term
  | `(fml($P))             => do `($P)
  | `($P:ident)              => do `($P)
  | `(?$P:ident)             => do `(?$P)
  | `(($P))                  => do `(($(← unpackCif P)))
  | `($P $[ $Q]*)            => do ``($P $[ $Q]*)
  | `(if $c then $t else $e) => do
    let t ← unpackCif t
    let e ← unpackCif e
    `(if $c then $t else $e)
  | `(($P : $t))             => do ``(($(← unpackCif P) : $t))
  | `($t)                    => `($t:term)

-- `fml` syntax interpretation
macro_rules
  | `(fml(⌜$φ⌝))      => ``(Fml.pure $φ)
  | `(fml($P ∧ $Q))   => ``(Fml.and fml($P) fml($Q))
  | `(fml($P ∨ $Q))   => ``(Fml.or fml($P) fml($Q))
  | `(fml($P → $Q))   => ``(Fml.imp fml($P) fml($Q))
  | `(fml(∃ $xs, $Ψ)) => do expandExplicitBinders ``Fml.ex xs (← ``(fml($Ψ)))
  | `(fml($P ∗ $Q))   => ``(Fml.sep fml($P) fml($Q))
  | `(fml($P -∗ $Q))  => ``(Fml.wand fml($P) fml($Q))
  | `(fml($P ∗-∗ $Q)) => ``(Fml.wandIff fml($P) fml($Q))
  | `(fml(<pers> $P)) => ``(Fml.pers fml($P))
  | `(fml(▷ $P))      => ``(Fml.later fml($P))
  | `(fml(|==> $P))  => ``(Fml.bupd iprop($P))
  | `(fml($P ==∗ $Q))  => ``(Fml.wand iprop($P) (Fml.bupd iprop($Q)))
  | `(fml(■ $P))  => ``(Fml.plain iprop($P))

delab_rule Fml.pure
  | `($_ $φ) => ``(fml(⌜$φ⌝))
delab_rule Fml.and
  | `($_ $P $Q) => do ``(fml($(← unpackCif P) ∧ $(← unpackCif Q)))
delab_rule Fml.or
  | `($_ $P $Q) => do ``(fml($(← unpackCif P) ∨ $(← unpackCif Q)))
delab_rule Fml.imp
  | `($_ $P $Q) => do ``(fml($(← unpackCif P) → $(← unpackCif Q)))
delab_rule Fml.all
  | `($_ $_:term fun $x:ident => fml(∀ $y:ident $[$z:ident]*, $Ψ)) => do
    ``(fml(∀ $x:ident $y:ident $[$z:ident]*, $Ψ))
  | `($_ $_:term fun $x:ident => $Ψ) => do ``(fml(∀ $x:ident, $(← unpackCif Ψ)))
delab_rule Fml.ex
  | `($_ $_:term fun $x:ident => fml(∃ $y:ident $[$z:ident]*, $Ψ)) => do
    ``(fml(∃ $x:ident $y:ident $[$z:ident]*, $Ψ))
  | `($_ $_:term fun $x:ident => $Ψ) => do ``(fml(∃ $x:ident, $(← unpackCif Ψ)))
delab_rule Fml.sep
  | `($_ $P $Q) => do ``(fml($(← unpackCif P) ∗ $(← unpackCif Q)))
delab_rule Fml.wand
  | `($_ $P $Q) => do ``(fml($(← unpackCif P) -∗ $(← unpackCif Q)))
delab_rule Fml.wandIff
  | `($_ $P $Q) => do ``(fml($(← unpackCif P) ∗-∗ $(← unpackCif Q)))
delab_rule Fml.pers
  | `($_ $P) => do ``(fml(<pers> $(← unpackCif P)))
delab_rule Fml.bupd
  | `($_ $P) => do ``(fml(|==> $(← unpackCif P)))
delab_rule Fml.plain
  | `($_ $P) => do ``(fml(■ $(← unpackCif P)))

delab_rule Fml.pure
  | `($_ True) => ``(fml($(mkIdent `True)))
  | `($_ False) => ``(fml($(mkIdent `False)))
delab_rule Fml.imp
  | `($_ $P fml(False)) => do ``(fml(¬$(← unpackCif P)))
  | `($_ $P $Q) => do ``(fml($(← unpackCif P) -> $(← unpackCif Q)))

/- This is necessary since the `∀` syntax is not defined using `explicitBinders` and we can
therefore not use `expandExplicitBinders` as for `∃`. -/
macro_rules
  | `(fml(∀ _%$tk, $Ψ)) => ``(Fml.all (fun _%$tk => fml($Ψ)))
macro_rules
  | `(fml(∀ $x:ident, $Ψ)) => ``(Fml.all (fun $x => fml($Ψ)))
macro_rules
  | `(fml(∀ (_%$tk : $t), $Ψ)) => ``(Fml.all (fun (_%$tk : $t) => fml($Ψ)))
  | `(fml(∀ (_%$tk $xs* : $t), $Ψ)) =>
    ``(Fml.all (fun (_%$tk : $t) => fml(∀ ($xs* : $t), $Ψ)))
macro_rules
  | `(fml(∀ ($x:ident : $t), $Ψ)) => ``(Fml.all (fun ($x : $t) => fml($Ψ)))
  | `(fml(∀ ($x:ident $xs* : $t), $Ψ)) =>
    ``(Fml.all (fun ($x : $t) => fml(∀ ($xs* : $t), $Ψ)))
macro_rules
  | `(fml(∀ {_%$tk : $t}, $Ψ)) =>
    ``(Fml.all (fun {_%$tk : $t}  => fml($Ψ)))
  | `(fml(∀ {_%$tk $xs* : $t}, $Ψ)) =>
    ``(Fml.all (fun {_%$tk : $t}  => fml(∀ {$xs* : $t}, $Ψ)))
macro_rules
  | `(fml(∀ {$x:ident : $t}, $Ψ)) =>
    ``(Fml.all (fun ($x : $t) => fml($Ψ)))
  | `(fml(∀ {$x:ident $xs* : $t}, $Ψ)) =>
    ``(Fml.all (fun ($x : $t) => fml(∀ {$xs* : $t}, $Ψ)))
macro_rules
  | `(fml(∀ $x $y $xs*, $Ψ)) => ``(fml(∀ $x, ∀ $y $xs*, $Ψ))

-- `fml` macros
macro_rules
  | `(fml(True))  => ``(Fml.pure True)
  | `(fml(False)) => ``(Fml.pure False)
  | `(fml(¬$P))   => ``(fml($P → False))

/-- Intuitionistic modality.
```
def intuitionistically (P) := <affine> <pers> P
```
-/

macro_rules
  | `(fml(◇ $P)) => ``(Fml.except0 fml($P))

delab_rule Fml.except0
  | `($_ $P) => do ``(fml(◇ $(← unpackCif P)))

def testCif1 : Fml FF :=
  Fml.all (fun (x : Nat) => Fml.all (fun (y : Nat) => Fml.pure (x < y)))

#print testCif1

def testCif2 : Fml FF :=
  fml(∀ (x : Nat), ⌜x = 1⌝)

#print testCif2

def testCif3 : Fml FF :=
  fml(∀ x (y : Nat), ⌜x < y⌝ -> ⌜¬ x ≥ y⌝)

#print testCif3
