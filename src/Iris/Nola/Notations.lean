import Iris.Nola.Syntax

open Lean

-- define `cif` embedding in `term`
syntax:max "cif(" term ")" : term
syntax:max "term(" term ")" : term

-- allow fallback to `term`
macro_rules
  | `(cif(term($t))) => pure t
  | `(cif($t))       => pure t

-- carry `cif` over some `term` constructs
macro_rules
  | `(cif(($P)))                  => ``((cif($P)))
  | `(cif(if $c then $t else $e)) => ``(if $c then cif($t) else cif($e))
  | `(cif(($P : $t)))             => ``((cif($P) : $t))

macro:max "cif(" P:term " : " t:term ")" : term => `((cif($P) : $t))

/-- Remove an `cif` quotation from a `term` syntax object. -/
partial def unpackCif [Monad m] [MonadRef m] [MonadQuotation m] : Term → m Term
  | `(cif($P))             => do `($P)
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

-- `cif` syntax interpretation
macro_rules
  | `(cif(⌜$φ⌝))      => ``(cif.pure $φ)
  | `(cif($P ∧ $Q))   => ``(cif.and cif($P) cif($Q))
  | `(cif($P ∨ $Q))   => ``(cif.or cif($P) cif($Q))
  | `(cif($P → $Q))   => ``(cif.imp cif($P) cif($Q))
  | `(cif(∃ $xs, $Ψ)) => do expandExplicitBinders ``cif.ex xs (← ``(cif($Ψ)))
  | `(cif($P ∗ $Q))   => ``(cif.sep cif($P) cif($Q))
  | `(cif($P -∗ $Q))  => ``(cif.wand cif($P) cif($Q))
  | `(cif($P ∗-∗ $Q)) => ``(cif.wandIff cif($P) cif($Q))
  | `(cif(<pers> $P)) => ``(cif.pers cif($P))
  | `(cif(▷ $P))      => ``(cif.later cif($P))

delab_rule cif.pure
  | `($_ $φ) => ``(cif(⌜$φ⌝))
delab_rule cif.and
  | `($_ $P $Q) => do ``(cif($(← unpackCif P) ∧ $(← unpackCif Q)))
delab_rule cif.or
  | `($_ $P $Q) => do ``(cif($(← unpackCif P) ∨ $(← unpackCif Q)))
delab_rule cif.imp
  | `($_ $P $Q) => do ``(cif($(← unpackCif P) → $(← unpackCif Q)))
delab_rule cif.all
  | `($_ $_:term fun $x:ident => cif(∀ $y:ident $[$z:ident]*, $Ψ)) => do
    ``(cif(∀ $x:ident $y:ident $[$z:ident]*, $Ψ))
  | `($_ $_:term fun $x:ident => $Ψ) => do ``(cif(∀ $x:ident, $(← unpackCif Ψ)))
delab_rule cif.ex
  | `($_ $_:term fun $x:ident => cif(∃ $y:ident $[$z:ident]*, $Ψ)) => do
    ``(cif(∃ $x:ident $y:ident $[$z:ident]*, $Ψ))
  | `($_ $_:term fun $x:ident => $Ψ) => do ``(cif(∃ $x:ident, $(← unpackCif Ψ)))
delab_rule cif.sep
  | `($_ $P $Q) => do ``(cif($(← unpackCif P) ∗ $(← unpackCif Q)))
delab_rule cif.wand
  | `($_ $P $Q) => do ``(cif($(← unpackCif P) -∗ $(← unpackCif Q)))
delab_rule cif.wandIff
  | `($_ $P $Q) => do ``(cif($(← unpackCif P) ∗-∗ $(← unpackCif Q)))
delab_rule cif.pers
  | `($_ $P) => do ``(cif(<pers> $(← unpackCif P)))

delab_rule cif.pure
  | `($_ True) => ``(cif($(mkIdent `True)))
  | `($_ False) => ``(cif($(mkIdent `False)))
delab_rule cif.imp
  | `($_ $P cif(False)) => do ``(cif(¬$(← unpackCif P)))
  | `($_ $P $Q) => do ``(cif($(← unpackCif P) -> $(← unpackCif Q)))

/- This is necessary since the `∀` syntax is not defined using `explicitBinders` and we can
therefore not use `expandExplicitBinders` as for `∃`. -/
macro_rules
  | `(cif(∀ _%$tk, $Ψ)) => ``(cif.all (fun _%$tk => cif($Ψ)))
macro_rules
  | `(cif(∀ $x:ident, $Ψ)) => ``(cif.all (fun $x => cif($Ψ)))
macro_rules
  | `(cif(∀ (_%$tk : $t), $Ψ)) => ``(cif.all (fun (_%$tk : $t) => cif($Ψ)))
  | `(cif(∀ (_%$tk $xs* : $t), $Ψ)) =>
    ``(cif.all (fun (_%$tk : $t) => cif(∀ ($xs* : $t), $Ψ)))
macro_rules
  | `(cif(∀ ($x:ident : $t), $Ψ)) => ``(cif.all (fun ($x : $t) => cif($Ψ)))
  | `(cif(∀ ($x:ident $xs* : $t), $Ψ)) =>
    ``(cif.all (fun ($x : $t) => cif(∀ ($xs* : $t), $Ψ)))
macro_rules
  | `(cif(∀ {_%$tk : $t}, $Ψ)) =>
    ``(cif.all (fun {_%$tk : $t}  => cif($Ψ)))
  | `(cif(∀ {_%$tk $xs* : $t}, $Ψ)) =>
    ``(cif.all (fun {_%$tk : $t}  => cif(∀ {$xs* : $t}, $Ψ)))
macro_rules
  | `(cif(∀ {$x:ident : $t}, $Ψ)) =>
    ``(cif.all (fun ($x : $t) => cif($Ψ)))
  | `(cif(∀ {$x:ident $xs* : $t}, $Ψ)) =>
    ``(cif.all (fun ($x : $t) => cif(∀ {$xs* : $t}, $Ψ)))
macro_rules
  | `(cif(∀ $x $y $xs*, $Ψ)) => ``(cif(∀ $x, ∀ $y $xs*, $Ψ))

-- `cif` macros
macro_rules
  | `(cif(True))  => ``(cif.pure True)
  | `(cif(False)) => ``(cif.pure False)
  | `(cif(¬$P))   => ``(cif($P → False))

/-- Intuitionistic modality.
```
def intuitionistically (P) := <affine> <pers> P
```
-/

macro_rules
  | `(cif(◇ $P)) => ``(cif.except0 cif($P))

delab_rule cif.except0
  | `($_ $P) => do ``(cif(◇ $(← unpackCif P)))

def testCif1 : cif FF :=
  cif.all (fun (x : Nat) => cif.all (fun (y : Nat) => cif.pure (x < y)))

#print testCif1

def testCif2 : cif FF :=
  cif(∀ (x : Nat), ⌜x = 1⌝)

#print testCif2

def testCif3 : cif FF :=
  cif(∀ x (y : Nat), ⌜x < y⌝ -> ⌜¬ x ≥ y⌝)

#print testCif3
