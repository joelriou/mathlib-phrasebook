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
between two such objects, a distinguished morphism from any object to
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

example : X ⟶ Z := f ≫ g -- type `≫` as `\gg`
example : X ⟶ X := 𝟙 X -- type `𝟙` as `\b1`
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
::: leanSection
```lean
universe v u -- `v` purposely appears first
variable {C : Type u} [Category.{v} C]
```
:::
Otherwise, `variable {C : Type*} [Category* C]` would register
two fresh arbitrary universes. Declaring a `u`-small category
can be done as
::: leanSection
```lean
variable {C : Type u} [SmallCategory C]
  -- this is equivalent to `[Category.{u} C]`
```
:::


A few examples of categories will be discussed in this phrasebook. One of
the basic examples if the category structure induced by a preorder. The
definitions `homOfLE` and `leOfHom` can be used in order to transform
an inequality `h : a ≤ b` into a morphism `a ⟶ b` in the category of
a preorder, and vice versa:
::: leanSection
```lean
variable {α : Type*} [Preorder α]
#synth SmallCategory α

example {a b : α} (h : a ≤ b) : a ⟶ b := homOfLE h
example {a b : α} (f : a ⟶ b) : a ≤ b := leOfHom f

```
:::

If `C` is a category, the opposite category is denoted `Cᵒᵖ`:
::: leanSection
```lean
variable {C : Type*} [Category* C]

open Opposite

example (X : C) : Cᵒᵖ := op X
example (X : Cᵒᵖ) : C := X.unop
example {X Y : C} (f : X ⟶ Y) : op Y ⟶ op X := f.op
example {X Y : Cᵒᵖ} (f : X ⟶ Y) : Y.unop ⟶ X.unop := f.unop
```
:::
The objects of `Cᵒᵖ` (and also the morphisms in `Cᵒᵖ`) are
implemented as a 1-field structure `Opposite`: we do not want
to enforce `Cᵒᵖ = C`, because it would create a confusion
about which `Category` instance on this type should be used.
Note that the type `Cᵒᵖᵒᵖ` is not equal to `C` either!

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
  slice_lhs 2 3 => rw [h]
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

# Functors and natural transformations

::: leanSection
```lean -show
variable {C D : Type*} [Category* C] [Category* D]
```

Assuming `C` and `D` are categories, the type `Functor C D`
of functors from `C` to `D` is denoted `C ⥤ D`, where
`⥤` is typed as `\functor`. The identity functor of the
category `C` is `𝟭 C` (where `𝟭` is typed as `\sb1`).
The composition of two functors `F : C₁ ⥤ C₂` and `G : C₂ ⥤ C₃`
is `F ⋙ G : C₁ ⥤ C₃` where `⋙` is typed as `\ggg`. Similarly as
for the composition of morphisms, this compostion `F ⋙ G` is
usually denoted `GF` is the mathematical literature.

For example, the identity functor is essentially defined
as follows:
```lean
variable (C) in
-- the actual definition in mathlib is `Functor.id`
@[simps, implicit_reducible]
def Functor.id' : C ⥤ C where
  obj (X : C) := X
  map {X Y : C} (f : X ⟶ Y) := f
  map_id := by cat_disch
```
The action of a functor on objects is `obj`, and its action of morphism
is `map`. There are two axioms `Functor.map_id` and `Functor.map_comp` in the
`Functor` structure, but they have `by cat_disch` as a default proof.
`cat_disch` is a tactic that is based on `aesop` which closes many
basic goals in category theory. In this case, it was able to show that
the identity functor preserves identity morphisms and the composition
of morphisms. Many such goals for other structures are also automatically
filled by this `cat_disch` tactic.

(The `implicit_reducible` attribute is required for definitions of essentially
all functors. Otherwise, when trying to prove equalities of morphisms involving
the action of functors, Lean may not be able to see through the `obj` fields
of functors. Basically, any definiton of a structure that has a field which
involves objects in a category should be declared `implicit_reducible`.)

The type `C ⥤ D` of functors is endowed with a category structure.
A morphism `f : F ⟶ G` from `F` to `G` in the category of functors `C ⥤ D`
is a natural transformation, i.e. a term in the type `NatTrans F G`.

```lean
variable {F G : C ⥤ D} (f : F ⟶ G)
example (X : C) : F.obj X ⟶ G.obj X := f.app X

/- the naturality of a natural transformation `f : F ⟶ G`
with respect to a morphism `g: X ⟶ Y` in `C` -/
example {X Y : C} (g : X ⟶ Y) :
    F.map g ≫ f.app Y = f.app X ≫ G.map g :=
  f.naturality g
```

Because Lean has a suitable hierarchy of universes, there is no
"set-theoretical" issue regarding the "existence" of functor categories.
Whatever the universes parameters for the categories `C` and `D` are
(and they may be different for `C` and `D`!), the type of functors `C ⥤ D`
and the type of natural transformation `F ⟶ G` between two functors in `C ⥤ D`
live in suitable universes.
:::

# Isomorphisms

::: leanSection
```lean -show
variable {C D : Type*} [Category* C] [Category* D]
```

An isomorphism between two objects `X` and `Y` in a category
`C` is a term `e` in the type `Iso X Y`, which is denoted `X ≅ Y`
(type `≅` as `\cong`). It involves a morphism `e.hom : X ⟶ Y` in
the forward direction, a morphism `e.inv : Y ⟶ X` in the backwards
direction and two axioms `e.hom_inv_id : e.hom ≫ e.inv = 𝟙 X` and
`e.inv_hom_id : e.inv ≫ e.hom = 𝟙 Y` (which Lean tries to auto-fill
`by cat_disch`). For example, the composition of two isomorphisms
is defined as follows:
```lean
variable {X Y Z : C} (e₁ : X ≅ Y) (e₂ : Y ≅ Z)

-- the definition is mathlib is `Iso.trans`,
-- and it is denoted `e₁ ≪≫ e₂`
@[simps]
def Iso.trans' : X ≅ Z where
  hom := e₁.hom ≫ e₂.hom
  inv := e₂.inv ≫ e₁.inv
```

In particular, if `F` and `G` are functors in `C ⥤ D`, we may say that
they are naturally isomorphic when we have `e : F ≅ G`:
```lean
variable {F G : C ⥤ D} (e : F ≅ G)
example (X : C) : F.obj X ≅ G.obj X := e.app X
```
:::

# The category of types

If `u` is a universe, `Type u` (which is the type of types in the universe `u`)
is a category. We tend to call it the category of types, but in the mathematical
literature, it may be referred to as the category of sets.
