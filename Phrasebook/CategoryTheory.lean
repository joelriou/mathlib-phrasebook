/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib
import Phrasebook.Meta.Lean
import VersoManual

open Phrasebook
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Category theory" =>

This page explains how to express common concepts in category theory
using the definitions in Mathlib.
We assume basic knowledge of both Lean and category theory.

Most of the definitions regarding general category theory are in
the `CategoryTheory` namespace. In order to use limits or colimits,
we need often need to open the `CategoryTheory.Limits` sub-namespace.
A typical file using category theory may contain:

```lean
open CategoryTheory Limits
```

The exposition is split in the following subsections:

# Category

A category involves a notion of objects, a notion of morphisms
between two such objects, a distinguished morphism from an object into
itself (the identity), the composition law of morphisms, and a few axioms.
In Mathlib, a category is thought as a structure on the type
of objects, and this structure involves a typeclass `Category`.

If we need to declare a category `C` as a variable, introduce
three objects `X`, `Y`, `Z`, two composable morphisms `f` from `X` to `Y`
and `g` from `Y` to `Z`, and consider the composition of `f` and `g`,
we proceed as follows:
::: leanSection
```lean
variable {C : Type*} [Category* C]
  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

example : X ⟶ Z := f ≫ g
```
In VScode, the arrow `⟶` that is used to denote the type of morphisms in a
category `C` is typed as `\hom` and it is different from the basic arrow `→`
(typed as `\to`) used for the type of nondependent functions between two types.

Note that the composition denoted here `f ≫ g` would usually be denoted "gf"
in the mathematical literature. Getting used to this notation is a
*rite of passage*. Beware that you may experience trouble going back to
the "gf" notation if you do too much formalization of category theory
in Lean.

The identity of an object `X` is denoted `𝟙 X`:
```lean
example : f ≫ 𝟙 Y = f := by simp
example : 𝟙 X ≫ f = f := by simp
```
:::

About universes, we may observe that in this implementation,
the types of morphisms in a category `C` (with `C : Type u`) can be
considered as a dependent function `C → C → Type v`: for each `X : C`
and `Y : C`, the type `X ⟶ Y` of morphisms from `X` to `Y`
belongs to `Type v` for a certain universe `v`. If we need to be specific
about these two universe parameters `u` (for objects) and
`v` (for morphisms), we do:
```lean
universe v u -- `v` purposely appears first
variable {C : Type u} [Category.{v} C]
```
Otherwise, `variable {C : Type*} [Category* C]` would register
two fresh arbitrary universes. Declaring a `u`-small category
can be done as
```
variable {C : Type u} [SmallCategory C]
  -- this is equivalent to `[Category.{u} C]`
```

# Associativity of the composition

::: leanSection
```lean -show
variable {C : Type*} [Category* C]
```

The composition of morphisms in a category is associative. When a term
is a composition of more than two morphisms, it is associated towards
the right, and this is also the `simp` normal form.

```lean

variable {X Y Z T : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

example : f ≫ g ≫ h = f ≫ (g ≫ h) := rfl
example : (f ≫ g) ≫ h = f ≫ g ≫ h := Category.assoc f g h
```

In non-formalized mathematics, the associativity of the composition
is often used implicitly. In formalized mathematics, we need to take
care about this associativity in one way or another when proving equalities
of morphisms:

```lean
variable {X₀ X₁ X₂ X₃ X₄ : C} (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂)
  (f₂ : X₂ ⟶ X₃) (f₃ : X₃ ⟶ X₄) (φ : X₁ ⟶ X₃)
  (h : f₁ ≫ f₂ = φ)

example : f₀ ≫ f₁ ≫ f₂ ≫ f₃ = f₀ ≫ φ ≫ f₃ := by
  rw [← Category.assoc f₁ f₂ f₃, h]
```

This proof uses the associativity in order to make the term `f₀ ≫ (f₁ ≫ f₂) ≫ f₃`
appear, which allows to rewrite `h`. Proceeding like this would be very unpractical
in more intricate cases, and it is also unconvenient because this would often
require using `Category.assoc` explicitly in both forward and backwards directions.
As it is a `simp` lemma, it is recommended to use it explicitly only in the forward direction.

An alternative proof can be obtained using specialized tactics:
```lean
example : f₀ ≫ f₁ ≫ f₂ ≫ f₃ = f₀ ≫ φ ≫ f₃ := by
  slice_lhs 2 3 => { rw [h] }
```
`slice_lhs` (and `slice_rhs`) are specialized `conv`-like tactics
which allow to zoom on certain chunks in the middle of compositions
of multiple morphisms. When there is no better way, this method
can be used when dealing with very long compositions.

In this case, the preferred proof would be:
```lean
example : f₀ ≫ f₁ ≫ f₂ ≫ f₃ = f₀ ≫ φ ≫ f₃ := by
  rw [reassoc_of% h]
```
This proof uses the term elaborator `reassoc_of%`: from an
an equality like `h : f₁ ≫ f₂ = φ`, it produces
a term `f₁ ≫ f₂ ≫ α = f₂ ≫ α` for a generic morphism `α`
which can be used in rewrites. Note that we do not need
the "dual" construction of a term `β ≫ f₁ ≫ f₂ = β ≫ f₂`
because `h` can be directly rewritten in it. Indeed,
this `reassoc_of% h` term could be rewritten in an
arbitrary composition like `β₀ ≫ ... ≫ βₙ ≫ f₁ ≫ f₂ ≫ γ₀ ≫ ... ≫ γₘ`
as soon as the list `[γ₀, ..., γₘ]` is nonempty.

Similarly, we have a `@[reassoc]` attribute (often used
in combination with `simp` as `@[reassoc (attr := simp)])`;
when it is applied to a lemma `foo`, it generates another
lemma `foo_assoc` similarly as `reassoc_of% h` is generated
from `h` above.

:::
