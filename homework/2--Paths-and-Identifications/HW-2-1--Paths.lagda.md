# Homework 2-1: Paths and the Interval

```
{-# OPTIONS --allow-unsolved-metas #-}
module homework.2--Paths-and-Identifications.HW-2-1--Paths where
open import Cubical.Core.Primitives public
open import Cubical.Data.Sigma.Base

open import homework.1--Type-Theory.HW-1-1--Types-and-Functions
open import homework.1--Type-Theory.HW-1-2--Inductive-Types
open import homework.1--Type-Theory.HW-1-3--Propositions-as-Types
-- open import homework-solutions.1--Type-Theory.1-3--Propositions-as-Types
```

Aside: This block lets us refer to some arbitrary types `A`, `B`, ... and
terms `x : A`, `y : A`, ... without cluttering every definition with
`{A : Type} {B : Type}`, and so on.
```
private
  variable
    ℓ : Level
    A B C D : Type ℓ
    S : A → Type ℓ
    x y z w : A
```

Topics covered:

* Paths as maps from the interval
  * The homotopical inspiration
* Basic paths:
  * Reflexivity
  * Function application (cong)
  * Paths in pair types
  * Paths in function types ("function extensionality")
* Substitution
* Paths as Equalities

References:
Cubical.Foundations.Prelude
Cubical.Foundations.GroupoidLaws
Cubical.Foundations.Path
https://github.com/mortberg/cubicaltt/blob/master/lectures/lecture2.ctt
https://1lab.dev/1Lab.Path.html#composition
https://1lab.dev/1Lab.Path.Groupoid.html#cubically

In Lecture 1-3, we saw that we could define types representing
equality in inductively defined types like `Bool` and `ℕ`. However, it
would be tedious to have to define equality separately for every type
(and worse, to check that every function preserves equality), and it
would make proving general facts about equality difficult.

To resolve this issue, Cubical Agda takes a page from homotopy theory
--- the mathematical theory of continuous deformations of
shapes. Classically, a *homotopy* is a continuous deformation of one
object into another. In homotopy theory, we only care about the
properties of objects which are unchanged by continuous deformation;
in other words, for the purposes of homotopy theory, to give a
homotopy between objects is to say that they are the same for all
homotopy theoretical purposes. That is, homotopies are ways to say two
things are the same.

Since we are looking for a general concept of sameness for all types,
it makes sense to take some ideas from homotopy theory. Let's see a
bit more of the classical theory first, so we have something to ground
our intuitions.

If $f$ and $g : X → Y$ are two continuous functions between spaces $X$
and $Y$ (say, subsets of $n$-dimensional Euclidean space), then a
homotopy $h$ between $f$ and $g$ is a function $h : [0, 1] × X → Y$ of
two variables $h(t, x)$ where $h(0, x) = f(x)$ and $h(1, x) = g(x)$
for all $x$. The intermediate values $h(t, x)$ continuously deform the
function $f$ into the function $g$.

(We use $ to delimit mathematical expressions as opposed to type
theoretical ones; admittedly the difference is not too important if
you are reading this in your editor.)

As we have seen in Lecture 1-1, we can think of a function of two
variables as a function of one variable landing in functions of one
variable. Using this idea, we can see a homotopy $h$ between $f$ and
$g$ as a function $h : [0, 1] → (X → Y)$ into the space of continuous
functions $X → Y$ where $h(0) = f$ and $h(1) = g$. In other words, a
homotopy is a *path* in function space, where a path is a continuous
function out of the unit interval $[0, 1]$. In general, if objects $F$
and $G$ are points of some space $S$, then a homotopy between $F$ and
$G$ is a path $h : [0, 1] → S$ with $h(0) = F$ and $h(1) = G$, no
matter what $F$ and $G$ are.


## Paths

This is the idea we will borrow for type theory. We will axiomatize a
special "type" `I` - meant to be our type theoretic version of the
unit interval $[0, 1]$ - with two elements `i0 : I` and `i1 : I`
(meant to be the endpoints $0$ and $1$). A *path* will then be a function
`h : I → S` into any type `S`. In general then, our notion of sameness
`x ≡ y` for any two elements `x y : S` will be a function `h : I → S`
with `h(i0) = x` and `h(i1) = y`. Crucially, these will be
*definitional* equalities; Agda will check that values of the function
on `i0` and `i1` match exactly with the ones specified.

-- ? My note starts
A path is defined as a function h : I → S that maps the elements of I
to a type S. This function h represents the path between two elements in S.
In other words, given two elements x and y in S, the notion of sameness or
equality between them, denoted as x ≡ y, is represented by a path
function h such that h(i0) = x and h(i1) = y.
-- ? My note ends

However, `I` is not like other types since we don't intend it to
represent a type of mathematical object. We are just using it as a
tool to get at a notion of sameness. For that reason, we silo it in
it's own special universe.

```
_ : IUniv
_ = I

_ : I
_ = i0

_ : I
_ = i1

```

This prevents us from using all our usual type operations on `I`, which
is good, since it isn't meant to be treated as a data type.
```
-- Uncomment these and try them out!
{-
_ : Type
_ = I × I  -- error!

_ : Type
_ = Bool → I -- error!
-}
```

However, since we want to discuss types of paths in any type, we have
the rule that for any type `A : Type`, the type `I → A` of functions from
`I` to `A` is a bona-fide type.

```
_ : Type
_ = I → Bool
```

Now we come to paths. Agda provides a built-in type `Path A x y` which
is like a function `I → A`, but where the endpoints are known to be
`x` and `y` *by definition*. That is, starting with `p : Path A x y`,
evaluating `p i0` gives *exactly* `x`, and evaluating `p i1` gives
*exactly* `y`. We will use the infix notation `x ≡ y` for `Path A x y`.
(To enter the ≡ symbol, write `\equiv`).

We define paths just like we define functions: we assume we have an
`i : I`, and then give an element of the type we are making the path
in. The simplest path we can come up with is the "reflexivity" path:
for any element `x`, there is a constant path at `x`.

```
refl : {A : Type ℓ} {x : A} → x ≡ x
refl {x = x} i = x
{-# INLINE refl #-}
```

Interpreted as a statement about sameness, this means that `x` is the
same as `x` - certainly a good start!

Even with such a basic principle, this is already enough to start
proving some useful equalities.
```
-- Exercise
∘-assoc : (h : C → D)
          (g : B → C)
          (f : A → B)
        → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
∘-assoc h g f = λ i x → h (g (f x))

-- Exercise
∘-idˡ : (f : A → B) → f ∘ (λ a → a) ≡ f
∘-idˡ f i x = f x

-- Exercise
∘-idʳ : (f : A → B) → (λ b → b) ∘ f ≡ f
∘-idʳ f i x = f x
```

We can even show that `Bool` has the structure of a *Boolean algebra*.
```
notnot : ∀ x → not (not x) ≡ x
notnot true = refl {x = true}
notnot false = refl {x = false}

-- or properties
or-zeroˡ : ∀ x → true or x ≡ true
or-zeroˡ _ = refl

or-zeroʳ : ∀ x → x or true ≡ true
or-zeroʳ true = refl
or-zeroʳ false = refl

or-identityˡ : ∀ x → false or x ≡ x
-- or-identityˡ x = refl
or-identityˡ _ = refl

or-identityʳ : ∀ x → x or false ≡ x
or-identityʳ true = refl
or-identityʳ false = refl

or-comm      : ∀ x y → x or y ≡ y or x
or-comm true true = refl
or-comm true false = refl
or-comm false true = refl
or-comm false false = refl

or-assoc     : ∀ x y z → x or (y or z) ≡ (x or y) or z
or-assoc true y z = refl
or-assoc false y z = refl
-- (y or z ≡ y or z)

or-idem      : ∀ x → x or x ≡ x
or-idem true = refl
or-idem false = refl
```

OK, that's enough of that --- it's straightforward to keep going.
(You can find all the laws for a Boolean algebra listed on Wikipedia,
or you can peek ahead to 2-2 and take all the laws for a De Morgan
algebra (but where `∧ = and` and `∨ = or` and `~ = not`) together with
the "Law of Excluded Middle": `b or (not b)`.)

Types of paths are types like any other, so we can define functions
that accept paths as arguments and produce paths as results.
```
cong : (f : A → B)
  → (x ≡ y)
  → f x ≡ f y
cong f p i = f (p i)
```
This is the principle that says that doing the same thing to both
sides of an equation gives an equal result - very useful!

```
-- Exercise: cong for binary functions
cong-bin : (f : A → B → C) {a a' : A} {b b' : B}
         → (p : a ≡ a')
         → (q : b ≡ b')
         → (f a b) ≡ (f a' b')
-- Exercise:
-- cong-bin f p q = λ i → cong f p i (q i) -- This works
cong-bin f p q = λ i → f (p i) (q i) -- Also works

cong-∘ : (f : A → B) (g : B → C)
  → (p : x ≡ y)
  → cong (g ∘ f) p ≡ cong g (cong f p)
-- Exercise:
-- Path between path
-- cong-∘ f g p i j = g (f (p j)) -- this works
cong-∘ f g p = refl
```

## Paths in Pairs and Function Types

Now we can begin to ask what paths look like in various types. We will
see what paths look like in inductive data types in more detail in
section 2-2. Let's begin with something easier: what is a path in a
pair type? It's a pair of paths of the components!

To prove these, remember that a path is secretly a function `I → ?`,
so ignoring the endpoints, the first is asking for a function `(I → A)
× (I → B) → (I → A × B)`. It should be easy to come up with such a
function, and it turns out the obvious definition has the correct
endpoints.

-- ? My note starts
≡-× takes two paths, one mapping I to type A and the other mapping
I to type B, and combines them to form a new function that maps I
to type A × B.

≡-fst takes a path between two pairs and extracts the path
between their first components.

≡-snd takes a path between two pairs and extracts the path
between their second components.
-- ? My note ends

```
≡-× : {x y : A × B} → (fst x ≡ fst y) × (snd x ≡ snd y) → x ≡ y
-- Exercise:
≡-× (p , q) i = (p i) , (q i)

≡-fst : {x y : A × B} → x ≡ y → (fst x ≡ fst y)
-- Exercise:
-- ≡-fst p = cong fst p -- This also works
≡-fst p i = fst (p i)

≡-snd : {x y : A × B} → x ≡ y → (snd x ≡ snd y)
-- Exercise:
≡-snd p i = snd (p i)
```

Similarly, what is a path in a function type? It is a function landing
in paths!

-- ? My note starts
Function type (A → B): a path in this type can be thought of as a function
that maps the interval to paths between the corresponding values in the codomain.

funExt: takes in an input function h mapping each x in A to a path between f x and g x.
It then returns a path proving the equality between f and g.
h itself is already of the type (x : A) → f x ≡ g x.

funExt⁻: takes in an input path p proving the equality between f and g. It then
returns a function that maps each x in A to a path between f x and g x.
-- ? My note ends

```
funExt : {f g : A → B}
  → ((x : A) → f x ≡ g x)
  -- if, for every input x : A, there exists a path between outputs f x and g x
  → f ≡ g -- then f and g are themselves equal
-- Exercise:
funExt h i x = h x i

funExt⁻ : {f g : A → B}
  → f ≡ g -- if f and g are equal functions
  → ((x : A) → f x ≡ g x)
  -- then there exists a function that maps each input x to a path between f x and g x
-- Exercise:
funExt⁻ p x i = p i x
```
This is the principle of "function extensionality": to say that `f`
equals `g` means that for all `x`, `f x` equals `g x`.

The `≡` constructor has low precedence, so `f x ≡ f y` means `(f x) ≡
(f y)`, and not something like `f (x ≡ f) y`.

```
-- Exercise: funExt for binary functions
funExt2 : {f g : A → B → C}
       (p : (x : A) (y : B) → f x y ≡ g x y)
       → f ≡ g
funExt2 p i x y = p x y i
```

## Isomorphisms

We have enough tools now to define an *isomorphism* between two
types. "Isomorphism" is a faux-Greek word meaning "same shape" ---
"iso-" and "morph". The idea of an isomorphism between two types is
that these types contain equivalent data.

Explicitly, an isomorphism between types `A` and `B` will be a pair
of maps `f : A → B` and `g : B → A` so that `f ∘ g ≡ id` and `g ∘ f ≡ 
id`. In other words, we can transform data of type `A` into data of
type `B` and vice versa, so that if we go from `A` to `B` and back
again, we get back to where we started.

If `f ∘ g ≡ id`, we say that `g` is a section of `f`, and if `g ∘ f ≡
id` we say that `g` is a retract of `f`. An isomorphism is therefore a
function `f : A → B` with in inverse map `g : B → A` where `g` is both
a section and a retract of `f`.

```
-- Section and retract
module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} where
  section : (f : A → B) → (g : B → A) → Type ℓ'
  section f g = ∀ b → f (g b) ≡ b
  -- Given an elem of type B, applying f to the corresponding elem in A
  -- (g b) yields the original elem

  -- NB: `g` is the retraction!
  retract : (f : A → B) → (g : B → A) → Type ℓ
  retract f g = ∀ a → g (f a) ≡ a
  -- Given an elem of type A, applying g to the corresponding elem in B
  -- (f a) yields the original elem

-- This defines a record type
-- Record types are like pair types, but more than two components.
-- All we need to know about this is that to build an Iso, we use
-- iso f g s r
record Iso {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor iso
  field
    fun : A → B -- f
    inv : B → A -- g
    rightInv : section fun inv
    leftInv  : retract fun inv
```

In section 1-2, we had a few "bijections" between types - now we can
show that these are really isomorphisms:

-- ? My note starts
Iso-Bool-⊤⊎⊤ is proving that the type Bool is isomorphic to the coproduct
type ⊤ ⊎ ⊤. An isomorphism between two types establishes an equivalence
or sameness of data between the two types. This means that we can transform
data of type Bool into data of type ⊤ ⊎ ⊤ and vice versa, while preserving
all relevant properties.
By showing that the composition of Bool→⊤⊎⊤ followed by ⊤⊎⊤→Bool (or vice versa)
results in the identity function, the isomorphism confirms that Bool and ⊤ ⊎ ⊤
are indeed equivalent in terms of the data they contain.
-- ? My note ends
```
-- Exercise:
-- s x = ?
-- r x = ?
Iso-Bool-⊤⊎⊤ : Iso Bool (⊤ ⊎ ⊤)
Iso-Bool-⊤⊎⊤ = iso Bool→⊤⊎⊤ ⊤⊎⊤→Bool s r
-- * fun = Bool→⊤⊎⊤ : Bool → ⊤ ⊎ ⊤
-- * inv = ⊤⊎⊤→Bool : ⊤ ⊎ ⊤ → Bool
-- * -> A = Bool, B = ⊤ ⊎ ⊤
-- * s = section fun inv = ∀ b → fun (inv b) ≡ b
-- * r = retract fun inv = ∀ a → inv (fun a) ≡ a
  where
    s : section Bool→⊤⊎⊤ ⊤⊎⊤→Bool
    -- ? This is proving that f ∘ g = id
    s (inl tt) = refl
    s (inr tt) = refl

    -- ? This is proving that g ∘ f = id
    r : retract Bool→⊤⊎⊤ ⊤⊎⊤→Bool
    r true = refl
    r false = refl
```

-- ? My note starts
Iso-∅⊎ establishes an isomorphism between the coproduct type ∅ ⊎ A
and the type A. This proves that the type ∅ ⊎ A containing either
an element of ∅ (the empty type) or an element of A is equivalent
to the type A itself.
-- ? My note ends
```
-- Exercise:
-- s x = ?
-- r x = ?
Iso-∅⊎ : ∀ {ℓ} (A : Type ℓ) → Iso (∅ ⊎ A) A
Iso-∅⊎ A = iso (∅⊎-to A) (∅⊎-fro A) s r
-- * fun = ∅⊎-to A : ∅ ⊎ A → A
-- * inv = ∅⊎-fro A : A → ∅ ⊎ A
-- * -> A = ∅ ⊎ A, B = A
-- * s = section fun inv = ∀ b → fun (inv b) ≡ b -- type A
-- * r = retract fun inv = ∀ a → inv (fun a) ≡ a -- type ∅ ⊎ A
  where
    s : section (∅⊎-to A) (∅⊎-fro A)
    s x = refl

    r : retract (∅⊎-to A) (∅⊎-fro A)
    -- r (inr a) i = inr a
    r (inr b) = λ i → inr b
```

-- ? My note starts
Iso-ℤ-ℕ⊎ℕ establishes an isomorphism between the integer type ℤ
and the coproduct type ℕ ⊎ ℕ. This proves that the set of integers
and the set of pairs of natural numbers (ℕ ⊎ ℕ) are equivalent.
-- ? My note ends
```
-- Exercise:
-- s x = ?
-- r x = ?
Iso-ℤ-ℕ⊎ℕ : Iso ℤ (ℕ ⊎ ℕ)
Iso-ℤ-ℕ⊎ℕ = iso ℤ→ℕ⊎ℕ ℕ⊎ℕ→ℤ s r
-- * fun = ℤ→ℕ⊎ℕ : ℤ → ℕ ⊎ ℕ
-- * inv = ℕ⊎ℕ→ℤ : ℕ ⊎ ℕ → ℤ
-- * -> A = ℕ, B = ℕ ⊎ ℕ
-- * s = section fun inv = ∀ b → fun (inv b) ≡ b -- type ℕ ⊎ ℕ
-- * = ℤ→ℕ⊎ℕ (ℕ⊎ℕ→ℤ [ℕ ⊎ ℕ]) -> ℕ⊎ℕ
-- * r = retract fun inv = ∀ a → inv (fun a) ≡ a -- type ℕ
-- * = ℕ⊎ℕ→ℤ (ℤ→ℕ⊎ℕ [ℕ]) -> ℕ
  where
    s : section ℤ→ℕ⊎ℕ ℕ⊎ℕ→ℤ
    -- s (inl a) i = inl a
    -- s (inr a) i = inr a
    s (inl a) = refl
    s (inr b) = refl

    r : retract ℤ→ℕ⊎ℕ ℕ⊎ℕ→ℤ
    -- r (pos n) i = pos n
    -- r (negsuc n) i = negsuc n
    r (pos n) = refl
    r (negsuc n) = refl
```

Not all isomorphisms will be so trivial. This one we need to construct
recursively.

```
-- Exercise:
-- s x = ?
-- r x = ?
Iso-ℕ-List⊤ : Iso ℕ (List ⊤)
Iso-ℕ-List⊤ = iso ℕ→List⊤ length s r
-- * fun = ℕ→List⊤ : ℕ → List ⊤
-- * inv = length : List ⊤ → ℕ
-- * -> A = ℕ, B = List ⊤
-- * s = section fun inv = ∀ b → fun (inv b) ≡ b -- type List ⊤
-- * = ℕ→List⊤ (length [List ⊤]) → List ⊤
-- * r = retract fun inv = ∀ a → inv (fun a) ≡ a -- type ℕ
-- * = length (ℕ→List⊤ [ℕ]) → ℕ
  where
    s : section ℕ→List⊤ length
    s [] = refl
    -- s (tt :: L) = λ i → tt :: (s L i) -- this works
    s (tt :: L) = cong (tt ::_) (s L)

    r : retract ℕ→List⊤ length
    r zero = refl
    r (suc x) = λ i → suc (r x i) -- ? try to see if there's alt
```

Not all isomorphisms have to go between different types. A type can be
isomorphic to itself in a non-trivial way.

```
-- Exercise
--  s x = ?
--  r x = ?
not-Iso : Iso Bool Bool
not-Iso = iso not not s r
  where
    s : section not not
    s true = refl
    s false = refl

    r : retract not not
    r true = refl
    r false = refl

-- Exercise
--  s x = ?
--  r x = ?
sucℤ-Iso : Iso ℤ ℤ
sucℤ-Iso = iso sucℤ predℤ s r
  where
    s : section sucℤ predℤ
    s (pos zero) = refl
    s (pos (suc n)) = refl
    s (negsuc zero) = refl
    s (negsuc (suc n)) = refl

    r : retract sucℤ predℤ
    r (pos zero) = refl
    r (pos (suc n)) = refl
    r (negsuc zero) = refl
    r (negsuc (suc n)) = refl
```

## Substitution and Paths as Equalities

Perhaps the most fundamental principle of equality is that we may
substitute equal things for equal things. Written out, substitution
should have this type signature:

`subst : (B : A → Type) (x ≡ y) → B x → B y` -- input: type dependent on another type + path

The idea here is that if `p : x ≡ y`, then `subst B p : B x → B y` is
the function that substitutes `x` for `y` in things of type `B x`
(whose definition may depend on `x`). Thinking of paths as equalities,
there is nothing we've seen yet that lets us do this. We'll need a new
primitive notion.

To see what we are missing, consider that we haven't said what a path
`I → Type` should be. Taking a cue from homotopy theory, we could
expect that a path between spaces would be a continuous deformation of
one space into another - a so-called "homotopy equivalence". In
particular, then, if we have such a path `A : I → Type`, we should be
able to "continuously move" an element `a : A i0` to some element of
`A i1`. This is called "transporting" the element `a` from `A i0` to
`A i1` along the path of types `A`.

Cubical Agda axiomatizes this idea with a function called `transp`:

`transp : ∀ (A : (i : I) (φ : I) → Type) (a : A i0) → A i1`
-- ? My note starts
A represents a family of types indexed by the interval I. Given a type
family A, an element a of type A at i0, and a path i0 ≡ i1 within the
interval, the transp function transports the element a along the path
to obtain an element of type A at i1.
-- ? My note ends

The function transp is slightly more general than what we need (we'll see what role the φ plays later in Part 2). What we really need is this function called "transport":

-- ? My note starts
transport:
- Input: equality p : A ≡ B between two types A and B, type A
- Goal: transport an element a from A to B along this equality
(output: element of type B)

- Input to transp:
  + type family (λ i → p i) - dependent type indexed by the
    interval I and parameterized by the path p.
  + index i0 - start of the interval, indicating the source type A
  + a is the element of type A that we want to transport
-- ? My note ends
```
transport : {A B : Type ℓ} → A ≡ B → A → B -- path + elem of first type -> elem of second type
transport p a = transp (λ i → p i) i0 a
```

With transport function, we can define subst by transporting in a
type family.

```
subst : (B : A → Type ℓ) (p : x ≡ y) → B x → B y
subst B p pa = transport (λ i → B (p i)) pa
```

Using substitution, we can show that there is no path from `true` to
`false` in `Bool`, and vice versa.

```
true≢false : ¬ true ≡ false -- ¬ == implies empty
true≢false p = subst (λ b → true ≡Bool b) p tt -- OG
-- ? Recall:
-- _≡Bool_ : (a b : Bool) → Type
-- true ≡Bool true = ⊤
-- true ≡Bool false = ∅
-- ? My notes
-- * subst B [dep. type] p [x ≡ y] pa [B x] → [B y]
-- = subst B p tt
-- B : true ≡Bool true = ⊤ & true ≡Bool false = ∅
-- p : true ≡ false
-- pa : tt = element of type ⊤ → B x = true ≡Bool [true] [this is x]
-- → Replace x [true] with y [false] (because p : true ≡ false)
-- * → B y = true ≡Bool false = ∅
```

Let's take a minute to make sure we really understand what's going on
here.

`true≢false` is a function `true ≡ false → ∅` --- to prove that `true`
doesn't equal `false`, we assume it does and derive an element of the
empty type, an absurdity! How do we do this?

Well, we have `true ≡Bool true = ⊤` and that `true ≡Bool false = ∅`,
both by definition. If `p : true ≡ false`, then we could replace the
second `true` in `true ≡Bool true` with `false` using substitution, to
get an element of `true ≡Bool false`, which would finish our proof. The type
family we are substituting in is therefore `(λ b → true ≡Bool b)`, and
so we get that `subst (λ b → true ≡Bool b) p : true ≡Bool true → true ≡Bool false`.

Give it a try in the reverse:
```
false≢true : ¬ false ≡ true
-- Exercise
false≢true p = subst (λ a → false ≡Bool a) p tt
-- ? My notes
-- false ≡Bool true = ∅
-- false ≡Bool false = ⊤
-- * subst B [dep. type] p [x ≡ y] pa [B x] → [B y]
-- * Goal: false ≡ true → ∅
-- Needs B s.t. replacing x [false] with y [true] causes B y = false
-- B y [true] = false ⇔ B : false ≡Bool [true] = ∅ → B : false ≡Bool _
-- pa : B x = false ≡Bool [false] = element of ⊤ = tt
```


Now we have all the tools necessary to show that paths in `Bool` are
the same thing as the equalities we define in 1-3!

```
≡iff≡Bool : (a b : Bool) → (a ≡ b) iffP (a ≡Bool b)
-- Exercise:
≡iff≡Bool a b = (to a b) , (fro a b)
  where
    to : (x y : Bool) → (x ≡ y) → (x ≡Bool y)
    to true true = λ _ → tt
    to true false = true≢false -- ? true ≡ false → ∅
    to false true = false≢true -- ? false ≡ true → ∅
    to false false = λ _ → tt

    fro : (x y : Bool) → (x ≡Bool y) → (x ≡ y)
    fro true true = λ _ → refl
    fro true false = ∅-rec -- mapping out of empty
    fro false true = ∅-rec
    fro false false = λ _ → refl
```

You might be wondering whether we could promote the two maps `to` and
`fro` above into an isomorphism between `a ≡ b` and `a ≡Bool b`. We
can, but we will need some theory developed in the next lecture. If
you're curious, give it a shot and see where you get stuck.

We can do the same for the other equalities we covered in 1-3.
-- ! Still need to revise from this point to the end
```
-- Exercise
-- to x y p = ?
-- fro x y p = ?
≡iff≡ℕ : (a b : ℕ) → (a ≡ b) iffP (a ≡ℕ b)
≡iff≡ℕ a b = (to a b) , (fro a b)
  where
    to : (x y : ℕ) → (x ≡ y) → (x ≡ℕ y)
    to zero zero p = tt
    -- to zero (suc y) p = subst isZeroP p tt -- works
    to zero (suc y) p = subst (λ z → zero ≡ℕ z) p tt
    to (suc x) zero p = subst (λ z → suc x ≡ℕ z) p (≡ℕ-refl x)
    to (suc x) (suc y) p = to x y (cong predℕ p)

    to' : (x y : ℕ) → (x ≡ y) → (x ≡ℕ y)
    to' x y p = subst (x ≡ℕ_) p (≡ℕ-refl x)

    fro : (x y : ℕ) → (x ≡ℕ y) → (x ≡ y)
    fro zero zero p = refl
    fro (suc x) (suc y) p = cong suc (fro x y p)
```

Now that we have a notion of sameness - paths - valid in all types, we
can resolve our conundrum concerning equalities in disjoint unions: we
can define them relative to the paths in the constituent halves of the
union.

```
_≡⊎_ : {A B : Type} (x y : A ⊎ B) → Type
inl a1 ≡⊎ inl a2 = a1 ≡ a2
inl a ≡⊎ inr b = ∅
inr b ≡⊎ inl a = ∅
inr b1 ≡⊎ inr b2 = b1 ≡ b2

refl⊎ : {A B : Type} (x : A ⊎ B) → x ≡⊎ x
refl⊎ (inl a) = refl
refl⊎ (inr b) = refl

-- Exercise
-- ≡iff≡⊎ x y = ?
-- Hint: can you see a way to define the forward direction using subst?
≡iff≡⊎ : {A B : Type} (x y : A ⊎ B) → (x ≡ y) iffP (x ≡⊎ y)
≡iff≡⊎ x y = (to x y) , (fro x y)
  where
    unl : (default : A) (x : A ⊎ B) → A
    unl _ (inl a) = a
    unl default (inr _) = default

    unr : (default : B) (x : A ⊎ B) → B
    unr _ (inr b) = b
    unr default (inl _) = default

    -- to : (x y : A ⊎ B) → (x ≡ y) → (x ≡⊎ y)
    -- to (inl a) (inl b) p = cong (unl a) p
    -- to (inl a) (inr b) p = subst (λ x → (inl a) ≡⊎ x ) p refl
    -- to (inr b) (inl a) p = subst (λ x → (inr b) ≡⊎ x) p refl
    -- to (inr b) (inr a) p = {!   !}

    to : (x y : A ⊎ B) → (x ≡ y) → (x ≡⊎ y)
    to x y p = subst (λ z → x ≡⊎ z) p ((refl⊎ x))

    fro : (x y : A ⊎ B) → (x ≡⊎ y) → (x ≡ y)
    fro (inl a) (inl b) p = cong inl p -- also works: inl (p i) -- applies to both side
    fro (inr b) (inr a) p = cong inr p
```

## Paths for integers ℤ
```
-- Equality
_≡ℤ_ : ℤ → ℤ → Type
pos n ≡ℤ pos m = n ≡ℕ m
pos n ≡ℤ negsuc m = ∅
negsuc n ≡ℤ pos m = ∅
negsuc n ≡ℤ negsuc m = n ≡ℕ m

-- Reflexitivity
≡ℤ-refl : {a : ℤ} → a ≡ℤ a
≡ℤ-refl {pos n} = ≡ℕ-refl n
≡ℤ-refl {negsuc n} = ≡ℕ-refl n

-- iff
≡iff≡ℤ : (a b : ℤ) → (a ≡ b) iffP (a ≡ℤ b)
≡iff≡ℤ a b = (to a b), (fro a b)
  where
    to : (x y : ℤ) → (x ≡ y) → (x ≡ℤ y)
    to x y p = subst (x ≡ℤ_) p ≡ℤ-refl

    fro : (x y : ℤ) → (x ≡ℤ y) → (x ≡ y)
    fro (pos n) (pos m) p = cong pos (≡iff≡ℕ n m .snd p) -- alt: snd (≡iff≡ℕ n m) p
    fro (negsuc n) (negsuc m) p = cong negsuc (≡iff≡ℕ n m .snd p)
```  