#import "@preview/curryst:0.6.0": prooftree, rule

#let cblue = rgb("1d4ed8")
#let c(..args) = {
  let pos = args.pos()
  if pos.len() == 0 { [] } else if pos.len() == 1 { text(fill: cblue, pos.first()) } else {
    text(fill: cblue, pos.join([, ]))
  }
}

// Domain-specific math operators and symbols
#let Lolly = math.class("relation", c($=compose$))
#let RLolly = math.class("relation", c($lt.o$))
#let FatArrow = math.class("relation", c($=>$))
#let RFatArrow = math.class("relation", c($arrow.l.double$))
#let qtensor = math.class("binary", c($times.o$))
#let aand = math.class("binary", c($amp$))
#let bigaand = math.class("large", c($amp$))
#let cscale = math.class("binary", c($dot$))
#let ceps = c($bold(epsilon)$)
#let cD = c($cal(D)$)
#let cL = c($cal(L)$)
#let packbox = $square$
#let vdashi = $⊢_i$
#let vdashs = $⊢_s$
#let vdashsimp = $⊢_s^a$
#let uplus = $⊎$
#let leadsto = math.arrow.squiggly
#let qquad = h(2em)

#let dsevidence(x) = $⟦ #x ⟧^bold("ev")$
#let dstype(..args) = $⟦ #args.pos().join([, ]) ⟧$

#let qed = math.square.stroked

#set document(
  title: "Linearly Qualified Types: Generic inference for capabilities and uniqueness",
  author: ("Arnaud Spiwack", "Csongor Kiss", "Jean-Philippe Bernardy", "Nicolas Wu", "Richard A. Eisenberg"),
)

#set heading(numbering: "1.1")

#align(center)[
  #v(1em)
  #text(1.7em, weight: "bold")[Linearly Qualified Types]\
  #v(0.3em)
  #text(1.2em, style: "italic")[Generic inference for capabilities and uniqueness]\
  #v(1em)

  #grid(
    columns: (1fr, 1fr, 1fr),
    gutter: 1em,
    [
      *Arnaud Spiwack*\
      Tweag, Paris, France\
      #link("mailto:arnaud.spiwack@tweag.io")
    ],
    [
      *Csongor Kiss*\
      Imperial College London, UK\
      #link("mailto:csongor.kiss14@imperial.ac.uk")
    ],
    [
      *Jean-Philippe Bernardy*\
      University of Gothenburg, Sweden\
      #link("mailto:jean-philippe.bernardy@gu.se")
    ],
  )
  #v(0.5em)
  #grid(
    columns: (1fr, 1fr),
    gutter: 1em,
    [
      *Nicolas Wu*\
      Imperial College London, UK\
      #link("mailto:n.wu@imperial.ac.uk")
    ],
    [
      *Richard A. Eisenberg*\
      Tweag, Paris, France\
      #link("mailto:rae@richarde.dev")
    ],
  )
  #v(1.5em)
]

#block(
  fill: rgb("f8fafc"),
  stroke: rgb("e2e8f0"),
  inset: 1.2em,
  radius: 4pt,
)[
  #align(center)[*Abstract*]
  A linear parameter must be consumed exactly once in the body of its function. When declaring resources such as file handles and manually managed memory as linear arguments, a linear type system can verify that these resources are used safely. However, writing code with explicit linear arguments requires bureaucracy.

  This paper presents _linear constraints_, a front-end feature for linear typing that decreases the bureaucracy of working with linear types. Linear constraints are implicit linear arguments that are filled in automatically by the compiler.

  We present linear constraints as a qualified type system, together with an inference algorithm which extends GHC's existing constraint solver algorithm. Soundness of linear constraints is ensured by the fact that they desugar into Linear Haskell.
]

#v(1em)

= Introduction
<sec:introduction>

Linear type systems have seen a renaissance in recent years in various programming communities. Rust's ownership system guarantees memory safety for systems programmers, Haskell's GHC 9.0 includes support for linear types, and even dependently typed programmers can now use linear types with Idris 2. All of these systems are vastly different in ergonomics and scope. Rust uses dedicated syntax and code generation to support management of resources, while Linear Haskell is a type system change without any other impact on the compiler, such as in the code generator or runtime system. Linear Haskell is designed to be general purpose, but using its linear arguments to emulate Rust's ownership model is a tedious exercise: it requires the programmer to carefully thread resource tokens.

To get a sense of the power and the tedium of using linear types, consider the following function:

```haskell
read2AndDiscard :: MArray a ⊸ (Ur a, Ur a)
read2AndDiscard arr0 =
  let (arr1, x) = read arr0 0
      (arr2, y) = read arr1 1
      ()        = free arr2
  in (x, y)
```

This function reads the first two elements of an array and returns them after deallocating the array. Linearity enables the array library to ensure that there is only one reference to the array, and therefore it can be mutated in-place without violating referential transparency. Let us stress that this uniqueness property is an invariant of the array library, not an intrinsic property of linear functions.

After the array has been freed, it is no longer possible to read or write to it. Notice that the `read` function consumes the array and returns a fresh array, to be used in future operations. Operationally, the array remains the same, but each operation assigns a new name to it, thus facilitating tracking references statically. Finally, `free` consumes the array without returning a new one, statically guaranteeing that it can no longer be used. The values `x` and `y` read from the array are returned; their types include elements wrapped by the `Ur` (pronounced "unrestricted", and corresponding to the "$!$" operator of Girard [1987]) type, allowing them to be used arbitrarily many times. This works because `read2AndDiscard` takes a restricted-use array containing unrestricted elements.

In a non-linear language, one would have to forgo referential transparency to handle mutable operations either by using a monadic interface or allowing arbitrary effects. Compare the above function with what one would write in a non-linear, impure language:

```haskell
read2AndDiscard :: MArray a -> (a, a)
read2AndDiscard arr =
  let x  = read arr 0
      y  = read arr 1
      () = unsafeFree arr
  in (x, y)
```

This non-linear version does not guarantee that there is a unique reference to the array, so freeing the array is a potentially unsafe operation. However, it is simpler because there is less bureaucracy to manage: we are clearly interacting with the _same_ array throughout, and this version makes that apparent. We see here a clear tension between extra safety and clarity of code—one we wish, as language designers, to avoid. How can we get the compiler to see that the array is used safely without explicit threading?

Following well-known ideas [Crary et al. 1999; Smith et al. 2000; Walker and Morrisett 2000], our approach is to let arrays be unrestricted, but associate linear capabilities (such as #c[`Read`], #c[`Write`]) to them. In fact, we show in this paper that such linear capabilities are the natural analogue of Haskell's type class constraints to the setting of linear types. We call these new constraints _linear constraints_. Like class constraints, linear constraints are propagated implicitly by the compiler. Like linear arguments, they can safely be used to track resources such as arrays or file handles. Thus, linear constraints are the combination of these two concepts, which have been studied independently elsewhere [Bernardy et al. 2017; Cervesato et al. 2000; Hodas and Miller 1994; Vytiniotis, Peyton Jones, Schrijvers, and Sulzmann 2011].

With our extension, we can write a new pure version of `read2AndDiscard` which does not require explicit threading of the array:

```haskell
read2AndDiscard :: (Read n, Write n) =⚬ UArray a n -> (Ur a, Ur a)
read2AndDiscard arr =
  let □ x  = read arr 0
      □ y  = read arr 1
      □ () = free arr
  in (x, y)
```

The only changes from the impure version are that this version explicitly requires having read and write access to the array, and pattern-matching against $packbox$ (read "pack") is necessary in order to access the linear constraint packed in the result of `read` and `free`. (Section 8.3 suggests how we can get rid of $packbox$, too.) Crucially, the resource representing the ownership of the array is a linear constraint and is separate from the array itself, which no longer needs to be threaded manually.

Our contributions are as follows:
- A system of qualified types that allows a constraint assumption to be given a multiplicity (linear or unrestricted). Linear assumptions are used precisely once in the body of a definition (@sec:qualified-type-system). This system supports examples that have motivated the design of several resource-aware systems, such as ownership à la Rust (@sec:memory-ownership), or capabilities in the style of Mezzo [Pottier and Protzenko 2013] or ATS [Zhu and Xi 2005]; accordingly, our system points towards a possible unification of these lines of research.
- Applications of this qualified type system to allow writing:
  - resource-aware algorithms without explicit threading (@sec:memory-ownership); and
  - functions whose result can only be used linearly (@sec:Unique-constraint).
- An inference algorithm that respects the multiplicity of assumptions. We prove that this algorithm is sound with respect to our type system (@sec:type-inference). It consists of:
  - a constraint generation algorithm (@sec:constraint-generation). The language of generated constraints tracks multiplicities.
  - a solver (@sec:constraint-solver) for the generated constraints, which restricts proof-search algorithms for linear logic in order to be _guess free_ [Vytiniotis, Peyton Jones, Schrijvers, and Sulzmann 2011, Section 6.4]. A guess-free algorithm ensures that constraint inference is predictable and insensitive to small changes in the source program; it is necessarily incomplete.

Our language is given semantics by desugaring into a core language based on that of Bernardy et al. [2017] (@sec:desugaring). Our design is intended to work well with other features of Haskell and GHC extensions. Indeed, we have a prototype implementation (@sec:implementation).
= Background: Linear Haskell
<sec:linear-types>

This section, mostly cribbed from Bernardy et al. [2017, Section 2.1], describes our baseline approach, as released in GHC 9.0. Linear Haskell adds a new type of functions, dubbed _linear functions_, and written $a ⊸ b$. A linear function consumes its argument exactly once. Linear Haskell defines it as follows:

#block(inset: (left: 1.5em))[
  $f :: a ⊸ b$ guarantees that if $(f space u)$ is consumed exactly once, then the argument $u$ is consumed exactly once.
]

To make sense of this statement we need to know what "consumed exactly once" means. Our definition is based on the type of the value concerned:

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Definition 2.1 (Consume exactly once).*
  - To consume a value of atomic base type (like `Int`) exactly once, just evaluate it.
  - To consume a function exactly once, apply it to one argument, and then consume its result exactly once.
  - To consume a pair exactly once, pattern-match on it, and then consume each component exactly once.
  - In general, to consume a value of an algebraic datatype exactly once, pattern-match on it, and then consume all its linear components exactly once.
]

== Multiplicities
<sec:multiplicities>

The usual arrow type $a -> b$ can be recovered using `Ur`, as $mono("Ur") space a ⊸ b$, but Linear Haskell provides a first-class treatment of $a -> b$, thus ensuring backwards compatibility with Haskell. In practice, the type-checker records the _multiplicity_ of every introduced variable: $1$ for linear arguments and $omega$ for unrestricted ones. This way, one can give a unified treatment of both arrow types [Kobayashi et al. 1999]:
$ pi, rho ::= 1 mid(|) omega quad text("Multiplicities") $

We stress that a multiplicity of $1$ restricts _how the variable can be used_. It does not restrict _which values can be substituted for it_. In particular, a linear function cannot assume that it is given the unique pointer to its argument. For example, if $f :: a ⊸ b$, then the following is fine:
```haskell
g :: a -> (b, b)
g x = (f x, f x)
```

The type of `g` makes no guarantees about how it uses `x`. In particular, `g` can pass `x` to `f`.

Pattern matching on a value of type `Ur a` yields a payload of multiplicity $omega$, even when the scrutinee has multiplicity $1$. In general, given a multiplicity set, the desired (sub)structural rules can be obtained by endowing multiplicities with the appropriate semiring structure [Abel and Bernardy 2020]. In this paper, we use the same multiplicity structure as Linear Haskell:
$
  pi + rho = omega
  quad quad
  cases(
    1 cscale pi = pi,
    omega cscale pi = omega,
  )
$

== Shortcomings of Linear Haskell that we address

The `read` function in @sec:introduction consumes the array it operates on. Therefore, the same array can no longer be used in further operations: doing so would result in a type error. To resolve this, a new name for the same array is produced by each operation.

From the perspective of the programmer, this is unwanted boilerplate. Minimizing such boilerplate is the main aim of this paper. Our approach is to let the array be non-linear, and let its capabilities (i.e. having read or write access) be _linear constraints_. Once these capabilities are consumed, the array can no longer be read from or written to without triggering a compile time error.

A further drawback of today's Linear Haskell is that the programmer cannot restrict how a linear function is used. For example, suppose we want to use linear types to create a pure interface to arrays that supports in-place mutation; the interface is safe only if we guarantee that arrays cannot be aliased. Because the result of a hypothetical `newArray` function can be stored in an unrestricted variable (of multiplicity $omega$), the linearity system cannot prevent its aliasing. Instead, Bernardy et al. [2017, Fig. 2] use a continuation-passing style to enforce non-aliasing.
= Working With Linear Constraints
<sec:what-it-looks-like>

Consider the Haskell function `show`:
```haskell
show :: Show a => a -> String
```

In addition to the function arrow `->`, common to all functional programming languages, the type of this function features a constraint arrow `=>`. Everything to the left of a constraint arrow is called a constraint, and will be highlighted in blue throughout the paper. Here #c[`Show a`] is a class constraint.

Constraints are handled implicitly by the typechecker. That is, if we want to show the integer `n :: Int` we would write `show n`, and the typechecker is responsible for proving that #c[`Show Int`] holds, without intervention from the programmer.

For our `read2AndDiscard` example, the #c[`(Read n, Write n)`] (abbreviated as #c[`RW n`]) constraint represents read and write access to the array tagged with the type variable $n$. (The full API under consideration appears in Figure 1b.) That is, the constraint #c[`RW n`] is provable if and only if the array tagged with $n$ is readable and writable. This constraint is linear: it must be consumed (that is, used as an assumption in a function call) exactly once. In order to manage linearity implicitly, this paper introduces a linear constraint arrow ($=compose$), much like Linear Haskell introduces a linear function arrow ($⊸$). Constraints to the left of a linear constraint arrow are _linear constraints_. Using the linear constraint #c[`RW n`], we can give the following type to `free`:

```haskell
free :: RW n =⚬ UArray a n -> ()
```

#v(0.5em)
#align(center)[
  #grid(
    columns: (1fr, 1.25fr),
    gutter: 1.5em,
    align: top + left,
    [
      *(a) Linear Types*
      ```haskell
      new   :: Int -> (MArray a ⊸ Ur r) ⊸ Ur r
      write :: MArray a ⊸ Int -> a -> MArray a
      read  :: MArray a ⊸ Int -> (MArray a, Ur a)
      free  :: MArray a ⊸ ()
      ```
    ],
    [
      *(b) Linear Constraints*
      ```haskell
      type RW n = (Read n, Write n)

      new   :: Linearly =⚬ Int
            -> ∃ n. UArray a n ⧀ RW n
      write :: RW n =⚬ UArray a n -> Int -> a
            -> () ⧀ RW n
      read  :: Read n =⚬ UArray a n -> Int
            -> Ur a ⧀ Read n
      free  :: RW n =⚬ UArray a n -> ()
      ```
    ],
  )
  *Figure 1: Interfaces for mutable arrays*
]
#v(0.5em)

There are a few things to notice:
- We have introduced a new type variable $n$. In contrast, the version in Figure 1a without linear constraints has type `free :: MArray a ⊸ ()`. The type variable $n$ is a type-level tag used to identify the array.
- The run-time variable representing the array can now be used multiple times. Instead of restricting the use of this variable, the linear constraint #c[`RW n`] controls access to the array.
- If we have a single, linear, #c[`RW n`] available, then after `free` there will not be any #c[`RW n`] left to use, thus preventing the array from being used after freeing. This is precisely what we were trying to achieve.

The above deals with freeing an array and ensuring that it cannot be used afterwards. However, we still need to explain how a constraint #c[`RW n`] can come into scope. The type of `new` with linear constraints is as follows:

```haskell
new :: Linearly =⚬ Int -> ∃ n. UArray a n ⧀ RW n
```

This type, too, illustrates several new aspects:
- The #c[`Linearly`] constraint is a linear constraint, though it takes no type parameter. It restricts the result of `new` to be used linearly, meaning that any variable that stores the result of `new` must have multiplicity $1$. #c[`Linearly`] is explained more fully in @sec:Unique-constraint.
- Because `UArray` is now parameterised by a type-level tag $n$, `new` must return a `UArray` with a fresh such $n$. This is achieved through returning an existentially-quantified type packing the type variable $n$. Such types are introduced with the $packbox$ constructor.
- Not only do we need a fresh type variable $n$, but we also need to introduce the linear constraint #c[`RW n`] for use in subsequent calls to `read` and `free`. Our existentials also allow packing a constraint, thanks to the $RLolly$ operator.

With all these features working together, we see that `new` returns a non-duplicable `UArray` tagged with $n$, accessible only when the #c[`RW n`] constraint is available.

We must also ensure that `read` can both promise to operate only on a readable array and that the array remains readable afterwards. That is, `read` must both consume a linear constraint #c[`Read n`] and also produce a fresh linear constraint #c[`Read n`], as we see in Figure 1b, and repeated here:

```haskell
read :: Read n =⚬ UArray a n -> Int -> Ur a ⧀ Read n
```

We have now seen all the ingredients needed to write the `read2AndDiscard` example as in @sec:introduction.

== Minimal Examples
<sec:examples>

To get a sense of how the features that we introduce should behave, we now look at some simple examples. Using constraints to represent limited resources allows the typechecker to reject certain classes of ill-behaved programs. Accordingly, the following examples show the different reasons a program might be rejected.

In what follows, we will be using a constraint #c[`C`] that is consumed by the `useC` function:

```haskell
useC :: C =⚬ Int
```

The type of `useC` indicates that it consumes the linear resource #c[`C`] exactly once.

=== Dithering
We reject this program:
```haskell
dithering :: C =⚬ Bool -> Int
dithering x = if x then useC else 10
```
The problem with `dithering` is that it does not unconditionally consume #c[`C`]: the branch where `x == True` uses the resource #c[`C`], whereas the other branch does not.

=== Neglecting
Now consider the type of the linear version of `const`:
```haskell
const :: a ⊸ b -> a
```
This function uses its first argument linearly, and ignores the second. Thus, the second arrow is unrestricted. One way to improperly use the linear `const` is by neglecting a linear variable:
```haskell
neglecting :: C =⚬ Int
neglecting = const 10 useC
```
The problem with `neglecting` is that, although `useC` is mentioned in this program, it is never consumed: `const` does not use its second argument. The constraint #c[`C`] is not consumed exactly once, and thus this program is rejected. The rule is that a linear constraint can only be consumed (linearly) in a linear context. For example,
```haskell
notNeglecting :: C =⚬ Int
notNeglecting = const useC 10
```
is accepted, because the #c[`C`] constraint is passed on to `useC` which itself appears as an argument to a linear function (whose result is itself consumed linearly).

=== Overusing
<sec:overusing>
Finally, the following program is rejected because it uses #c[`C`] twice:
```haskell
overusing :: C =⚬ (Int, Int)
overusing = (useC, useC)
```

== Restricting to a linear context with #c[`Linearly`]
<sec:Unique-constraint>

A linear function makes a promise about how it is going to use its argument, but linearity imposes no restrictions on how a function – or its result – is going to be used. The caller may use the linear function's result unrestrictedly. This poses a challenge for providing a type-safe interface for libraries that rely on having a unique pointer to some resource, such as safe mutable arrays, because the obvious definition of a constructor function can immediately be misused, violating the assumption of uniqueness:

```haskell
new :: Int -> MArray a
bad = let arr = new 5 in (arr, arr)
badToo = Ur (new 5)
```

However, with linear constraints, we can overcome this problem by putting the special #c[`Linearly`] constraint on `new`:

```haskell
new :: Linearly =⚬ Int -> MArray a
```

Suppose we have assumed the #c[`Linearly`] constraint linearly; that is, we must use the #c[`Linearly`] assumption precisely once. Now, our definition for `bad` is rejected: either we infer `arr` to have multiplicity $omega$, in which case its definition uses #c[`Linearly`] $omega$ times; or we infer `arr` to have multiplicity $1$, in which case its use (twice) violates the linearity restriction. Likewise, the use of `Ur` in `badToo` requires using the #c[`Linearly`] assumption $omega$ times.

This is promising so far, but several problems remain:

*Duplicating #c[`Linearly`].* What if we want to create multiple arrays, each of which having a unique pointer? If #c[`Linearly`] is assumed linearly, then `let arr1 = new 5; arr2 = new 6` will fail, as it uses our #c[`Linearly`] assumption twice. We thus stipulate that #c[`Linearly`] must itself be duplicable: from one assumption of #c[`Linearly`], we must be able to satisfy any arbitrary fixed number of demands on that constraint. By "arbitrary fixed number", we mean to say that we can duplicate #c[`Linearly`] a finite number of times, but we may not use an assumption of #c[`Linearly`] with multiplicity $1$ to satisfy #c[`Linearly`] at multiplicity $omega$.

*Discarding #c[`Linearly`].* Similarly to allowing duplication, we must allow discarding, in case a function allocates no arrays at all. Accordingly, we allow a linear assumption of #c[`Linearly`] to be accepted even if the constraint is never used.

*Initial assumption of #c[`Linearly`].* For this approach to work, we must have an assumption of #c[`Linearly`] of multiplicity $1$. We can achieve this via the following primitive:

```haskell
linearly :: (Linearly =⚬ Ur r) ⊸ Ur r
```

The argument to `linearly` will be a continuation that assumes #c[`Linearly`] with multiplicity $1$. Because `linearly` returns an unrestricted value, no restricted values from the continuation can escape the scope of the #c[`Linearly`] assumption. Thus, the continuation has exactly the condition we need: a linear assumption of #c[`Linearly`].

The pattern of using a continuation in `linearly` mirrors the use of that technique by Bernardy et al. [2017, Fig. 2]. But `linearly` is, now, the only place where we need a continuation: once we have our linear #c[`Linearly`] assumption, we can use it to produce new values that must be unique.

With just these simple ingredients – a duplicable, discardable constraint that can be assumed linearly – we can write APIs that require uniqueness without heavy use of continuations.
= Application: Memory Ownership
<sec:memory-ownership>

Let us now turn back to the more substantial example introduced in Section 1: manual memory management. In functional programming languages like Haskell, memory deallocation is normally the responsibility of a garbage collector. However, garbage collection is not always desirable, either due to its (unpredictable) runtime costs, or because pointers exist between separately-managed memory spaces (for example when calling foreign functions [Domínguez 2020]). In either case, one must then resort to explicit memory allocation and deallocation. This task is error prone: one can easily forget a deallocation (causing a memory leak) or deallocate several times (corrupting data). In this section we show how to build a memory management API as a library using linear constraints. The library is a generalisation of the array library introduced in Section 1.

== Capability constraints
<sec:atomic-references>

Our approach, inspired by Rust, is to represent ownership of a memory location, and more specifically, whether the reference is mutable or read-only. We use the linear constraints #c[`Read n`] and #c[`Write n`], guarding read access and write access to a reference respectively. Because of linearity, these constraints must be consumed, so the API can guarantee that memory is deallocated correctly. In #c[`Read n`], $n$ is a type variable (of a special kind `Location`) which represents a memory location. Locations mediate the relationship between references and ownership constraints.

```haskell
class Read  (n :: Location)
class Write (n :: Location)
```

To ensure referential transparency, writes can be done only when we are sure that no other part of the program has read access to the reference. Therefore, writing also requires the read capability. Thus we systematically use #c[`RW n`], pairing both the read and write capabilities:

```haskell
type RW n = (Read n, Write n)
```

With these components in place, we can provide an API for mutable references:

```haskell
data AtomRef (a :: Type) (n :: Location)
```

The type `AtomRef` is the type of references to values of a type $a$ at location $n$. Allocation of a reference can be done using the following function:

```haskell
newRef :: Linearly =⚬ ∃ n. AtomRef a n ⧀ RW n
```

The function `newRef` creates a new atomic reference, initialised with $bot$; we could also pass in an initial value, but doing so in the more general case below would add complication and obscure our main goal of demonstrating linear constraints.

To read a reference, a #c[`Read`] constraint is demanded, and then returned back. Writing is similar:

```haskell
readRef  :: Read n =⚬ AtomRef a n -> Ur a ⧀ Read n
writeRef :: RW n   =⚬ AtomRef a n -> a -> () ⧀ RW n
```

Note that the above primitives do not need to explicitly declare effects in terms of a monad or another higher-order effect-tracking device: because the #c[`RW n`] constraint is linear, passing it suffices to ensure proper sequencing of effects concerning location $n$.

Also note that `readRef` returns an unrestricted copy of the element, and `writeRef` copies an unrestricted element into the location. This means that while `AtomRef`s are mutable, their contents are always immutable structures.

Since there is a unique #c[`RW n`] constraint per reference, we can also use it to represent ownership of the reference: access to #c[`RW n`] represents responsibility (and obligation) to deallocate $n$:

```haskell
freeRef :: RW n =⚬ AtomRef a n -> ()
```

== Arrays
<sec:arrays>

The above toolkit handles references to base types just fine. But what about storing references in objects managed by the ownership system? In Section 1, we presented an interface for mutable arrays whose contents are themselves immutable. Our approach scales beyond that use case, supporting arrays of references, including arrays of (mutable) arrays.

```haskell
data PArray (a :: Location -> Type) (n :: Location)
newPArray :: Linearly =⚬ Int -> ∃ n. PArray a n ⧀ RW n
```

For this purpose we introduce the type `PArray a n`, where the kind of $a$ is `Location -> Type`: this way we can easily enforce that each reference in the array refers to the same location $n$. Both types `AtomRef a` and `PArray a` have kind `Location -> Type`, and therefore one can allocate, and manipulate arrays of arrays with this API. For example, an array of integers has type `PArray (AtomRef Int) n`, and indeed, the `UArray` type from Section 1 is a synonym for an array of atomic references. An array of arrays of integers would have type `PArray (PArray (AtomRef Int)) n`. Thus, the framework handles nested mutable structures without any additional difficulty.

The actual runtime value of a `PArray` is a pointer to a contiguous block of memory together with the size of the memory block. This means that the length of the array can be accessed without having ownership of the array:

```haskell
length :: PArray a n -> Int
```

While the `PArray` reference itself is managed by the garbage collector, the pointer it contains points to manually managed memory.

=== Borrowing
<sec:borrowing>

The `lendMut arr i k` primitive lends access to the reference at index $i$ in `arr`, to a continuation function $k$ (in Rust terminology, the function borrows an element of the array). Note that the continuation must return the read-write capability, so that the ownership transfer is indeed temporary. The type system guarantees that the borrowed reference cannot be shared or deallocated. Indeed, with this API, #c[`RW n`] and #c[`RW p`] are never simultaneously available.

```haskell
lendMut :: RW n =⚬ PArray a n -> Int
        -> (∀ p. RW p =⚬ a p -> r ⧀ RW p) ⊸ r ⧀ RW n
```

Because the elements of an array can be mutable structures (such as other arrays), reading can be done safely only if we can ensure that no one else has access to the array while the element is accessed. Otherwise, the array – including the element being read – could be mutated. Therefore, gaining simple read access to an element needs to be done using a scoped API as well:

```haskell
lend :: Read n =⚬ PArray a n -> Int
     -> (∀ p. Read p =⚬ a p -> r ⧀ Read p) ⊸ r ⧀ Read n
```

For the special case of `UArray`s, a more traditional reading operation can be implemented, by lending the reference to `readRef` which creates an unrestricted copy of the value. This copy is under control of the garbage collector, and can escape the scope of the borrowing freely:

```haskell
read :: Read n =⚬ UArray a n -> Int -> Ur a ⧀ Read n
read arr i = lend arr i readRef
```

=== Slices
<sec:slices>

It is also possible to give a safe interface to array slices. A slice represents a part of an array and allows splitting the ownership of the array into multiple parts, shared between different consumers. The ownership system means that slicing does not require copying.

Splitting consumes all capabilities of an array and returns two new arrays that represent the contiguous blocks of memory before and starting at a given index:

```haskell
split :: RW n =⚬ PArray a n -> Int
      -> ∃ l r. Ur (PArray a l, PArray a r) ⧀ (RW l, RW r, Slices n l r)
```

In addition to the array capabilities, the output constraints also include #c[`Slices n l r`], witnessing the fact that locations $l$ and $r$ are components of $n$, so that they can be joined back together:

```haskell
join :: (Slices n l r, RW r, RW l) =⚬ PArray a l -> PArray a r
     -> Ur (PArray a n) ⧀ RW n
```

#v(0.5em)
#align(center)[
  #block(
    fill: rgb("fafafa"),
    inset: 1em,
    stroke: 0.5pt + luma(200),
    radius: 3pt,
  )[
    #align(left)[
      *Figure 2: Swapping two elements of an array*
      ```haskell
      swap :: RW n =⚬ PArray AtomRef n -> Int -> Int -> () ⧀ RW n
      swap arr i j
        | i == j    = □ ()
        | i >  j    = swap arr j i
        | i <  j    =
            let □ (Ur (l, r)) = split arr (i + 1)
                □ ()          = lendMut l i (\a_i ->
                                  let □ () = lendMut r (j - (i + 1)) (\a_j ->
                                        let □ (Ur a_i_val) = readRef a_i
                                            □ (Ur a_j_val) = readRef a_j
                                            □ ()           = writeRef a_j a_i_val
                                            □ ()           = writeRef a_i a_j_val
                                        in □ ()) in □ ())
                □ (Ur _)      = join l r
            in □ ()
      ```
    ]
  ]
]
#v(0.5em)

With these building blocks, we can now implement various utility functions on arrays, such as swapping two elements of an array, which is shown in Figure 2. It is not so simple to implement (indeed, Rust's implementation uses an `unsafe` block), because we need two elements of an array simultaneously, but only one element can be borrowed at a time. To solve this problem, we split the array into two slices such that the two indices fall in two different slices. Then simply borrow the element $i$ from the first slice, and $j$ from the second slice (using `lendMut`). Finally, we join the two slices back together.

=== In-place Quicksort
<sec:quicksort>

As an example of using the machinery defined above, we implement an in-place, pure quicksort algorithm, given in Figure 3. The `partition` function is responsible for picking a pivot element and reorganising the array elements such that each element preceding the pivot will be less than or equal to it, and the elements after will be greater than the pivot. Once finished, it returns the index of the pivot element; `sort` then splits the array at the pivot element and recursively operates on the two slices.

#v(0.5em)
#align(center)[
  #block(
    fill: rgb("fafafa"),
    inset: 1em,
    stroke: 0.5pt + luma(200),
    radius: 3pt,
  )[
    #align(left)[
      *Figure 3: In-place quicksort*
      #v(0.5em)
      #grid(
        columns: (1fr, 1.25fr),
        gutter: 1.5em,
        align: top + left,
        [
          ```haskell
          sort :: RW n =⚬ UArray Int n -> () ⧀ RW n
          sort arr =
            let len = length arr in
            if len <= 1 then □ ()
            else
              let □ pivotIdx    = partition arr
                  □ (Ur (l, r)) = split arr pivotIdx
                  □ ()          = sort l
                  □ ()          = sort r
                  □ (Ur _)      = join l r
              in □ ()
          ```
        ],
        [
          ```haskell
          partition :: RW n =⚬ UArray Int n -> Int ⧀ RW n
          partition arr =
            let last         = length arr - 1
                □ (Ur pivot) = read arr last
                go :: RW n =⚬ Int -> Int -> Int ⧀ RW n
                go l r
                  | l > r     = let □ () = swap arr last l
                                in □ l
                  | otherwise =
                      let □ (Ur lVal) = read arr l in
                      if lVal > pivot
                      then let □ () = swap arr l r
                           in go l (r - 1)
                      else go (l + 1) r
            in go 0 (last - 1)
          ```
        ],
      )
    ]
  ]
]
= A Qualified Type System for Linear Constraints
<sec:qualified-type-system>

We now present our design for a qualified type system [Jones 1994] that supports linear constraints. Our design, based on the work of Vytiniotis, Peyton Jones, Schrijvers, and Sulzmann [2011], is compatible with Haskell and GHC.

== Simple Constraints and Entailment
<sec:constraint-domain>

We call constraints such as #c[`Read n`] or #c[`Write n`] _atomic constraints_. The set of atomic constraints is a parameter of our qualified type system.

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Definition 5.1 (Atomic constraints).*
  The qualified type system is parameterised by a set, whose elements are called atomic constraints. We use the variable #c[$q$] to denote atomic constraints.
]

Atomic constraints are assembled into simple constraints #c[$Q$], which play the hybrid role of constraint contexts and (linear) logic formulae. The following operations work with simple constraints:

- *Scaled atomic constraints:* #c[$pi cscale q$] is a simple constraint, where $pi$ specifies whether #c[$q$] is to be used linearly or not.
- *Conjunction:* Two simple constraints can be paired up #c[$Q_1 qtensor Q_2$]. Semantically, this corresponds to the multiplicative conjunction of linear logic. Tensor products represent pairs of constraints such as `(Read n, Write n)` from Haskell.
- *Empty conjunction:* Finally we need a neutral element $ceps$ to the tensor product. The empty conjunction is used to represent functions which don't require any constraints.

However, we do not define #c[$Q$] inductively, because we require certain equalities to hold:
$
  #c[$Q_1 qtensor Q_2$] &= #c[$Q_2 qtensor Q_1$] quad quad &#c[$(Q_1 qtensor Q_2) qtensor Q_3$] &= #c[$Q_1 qtensor (Q_2 qtensor Q_3)$] \
  #c[$omega cscale q qtensor omega cscale q$] &= #c[$omega cscale q$] &#c[$Q qtensor ceps$] &= #c[$Q$]
$

We thus say that a simple constraint is a pair combining a set of unrestricted constraints #c[$U$] and a multiset of linear constraints #c[$L$]. The linear constraints must be stored in a multiset, because assuming the same constraint twice is distinct from assuming it only once.

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Definition 5.2 (Simple constraints).*
  $
    #c[$U$] & ::= dots quad text("set of atomic constraints " c(q)) \
    #c[$L$] & ::= dots quad text("multiset of atomic constraints " c(q)) \
    #c[$Q$] & ::= #c[$(U, L)$] quad text("simple constraints")
  $
  We can now straightforwardly define the operations we need on simple constraints:
  $
    ceps = #c[$(emptyset, emptyset)$] quad quad
    cases(
      #c[$1 cscale q$] = #c[$(emptyset, {q})$],
      #c[$omega cscale q$] = #c[$({q}, emptyset)$],
    ) quad quad
    #c[$(U_1, L_1) qtensor (U_2, L_2)$] = #c[$(U_1 union U_2, L_1 uplus L_2)$]
  $
]

In practice, we do not need to concern ourselves with the concrete representation of #c[$Q$] as a pair of sets, instead using the operations defined just above.

The semantics of simple constraints (and, indeed, of atomic constraints) is given by an entailment relation. Just like the set of atomic constraints, the entailment relation is a parameter of our system.

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Definition 5.3 (Entailment relation).*
  The qualified type system is parameterised by a relation #c[$Q_1$] $⊩$ #c[$Q_2$] between two simple constraints, as well as by a distinguished set #c[$cal(D)$] of duplicable atomic constraints.

  We write, abusing notation, #c[$Q in cal(D)$] for a simple constraint #c[$Q = (U, L)$] if for all #c[$q in L$] we have #c[$q in cal(D)$].
]

#v(0.5em)
#align(center)[
  #block(
    fill: rgb("fafafa"),
    inset: 1em,
    stroke: 0.5pt + luma(200),
    radius: 3pt,
  )[
    #align(left)[
      *Figure 4: Requirements for the entailment relation #c[$Q_1$] $⊩$ #c[$Q_2$]*
      #v(0.5em)
      1. #c[$Q$] $⊩$ #c[$Q$]
      2. If #c[$Q_1$] $⊩$ #c[$Q_2$] and #c[$Q qtensor Q_2$] $⊩$ #c[$Q_3$], then #c[$Q qtensor Q_1$] $⊩$ #c[$Q_3$].
      3. If #c[$Q$] $⊩$ #c[$Q_1 qtensor Q_2$], then there exist #c[$Q'$], #c[$Q_cal(D)$], and #c[$Q''$] such that #c[$Q_cal(D) in cal(D)$], #c[$Q$] $= #c[$Q' qtensor Q_cal(D) qtensor Q''$]$, #c[$Q' qtensor Q_cal(D)$] $⊩$ #c[$Q_1$], and #c[$Q_cal(D) qtensor Q''$] $⊩$ #c[$Q_2$].
      4. If #c[$Q$] $⊩ ceps$, then #c[$Q in cal(D)$].
      5. If #c[$Q_1$] $⊩$ #c[$Q'_1$] and #c[$Q_2$] $⊩$ #c[$Q'_2$], then #c[$Q_1 qtensor Q_2$] $⊩$ #c[$Q'_1 qtensor Q'_2$].
      6. If #c[$Q$] $⊩$ #c[$rho cscale q$], then #c[$pi cscale Q$] $⊩$ #c[$(pi cscale rho) cscale q$].
      7. If #c[$Q$] $⊩$ #c[$(pi cscale rho) cscale q$], then there exists #c[$Q'$] such that #c[$Q$] $= #c[$pi cscale Q'$]$ and #c[$Q'$] $⊩$ #c[$rho cscale q$].
      8. If #c[$Q_1$] $⊩$ #c[$Q_2$], then #c[$omega cscale Q_1$] $⊩$ #c[$Q_2$].
      9. If #c[$Q_1$] $⊩$ #c[$Q_2$], then for all #c[$Q'$], it is the case that #c[$omega cscale Q' qtensor Q_1$] $⊩$ #c[$Q_2$].
      10. If #c[$q in cal(D)$], then #c[$1 cscale q$] $⊩$ #c[$1 cscale q qtensor 1 cscale q$].
      11. If #c[$q in cal(D)$], then #c[$1 cscale q$] $⊩ ceps$.
      12. If #c[$Q in cal(D)$] and #c[$Q'$] $⊩$ #c[$Q$], then #c[$Q' in cal(D)$].
    ]
  ]
]
#v(0.5em)

The entailment relation must obey the laws listed in Figure 4.

The set #c[$cal(D)$] is a set of constraints which can be duplicated and discarded (see Figure 4). We use #c[$cal(D)$] to model the #c[`Linearly`] constraint. Crucially, it is not the case that #c[$1 cscale q$] $⊩$ #c[$omega cscale q$] for #c[$q in cal(D)$]; such an entailment is, in fact, prohibited (Lemma 5.5) by the rules of Figure 4. While it may seem counter-intuitive, there is nothing in linear logic mandating that a formula that can be duplicated and discarded be (equivalent to) an unrestricted formula. This observation has been exploited, for instance, to introduce so-called subexponentials [Danos et al. 1993]. For our use case, it lets the typechecker dispatch #c[`Linearly`] constraints (using duplication), but prevents the result of constrained functions to be used unrestrictedly.

An important feature of simple constraints is that, while scaling syntactically happens at the level of atomic constraints, these properties of scaling extend to scaling of arbitrary constraints. Define #c[$pi cscale Q$] as:
$
  cases(
    #c[$1 cscale (U, L)$] = #c[$(U, L)$],
    #c[$omega cscale (U, L)$] = #c[$(U union L, emptyset)$],
  )
$

Then the following properties hold:

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Lemma 5.4 (Scaling).* If #c[$Q_1$] $⊩$ #c[$Q_2$], then #c[$pi cscale Q_1$] $⊩$ #c[$pi cscale Q_2$].
]

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Lemma 5.5 (Inversion of scaling).* If #c[$Q_1$] $⊩$ #c[$pi cscale Q_2$], then #c[$Q_1$] $= #c[$pi cscale Q'$]$ and #c[$Q'$] $⊩$ #c[$Q_2$] for some #c[$Q'$].
]

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Corollary 5.6 (Linear assumptions).* If #c[$Q_1$] $⊩$ #c[$omega cscale Q_2$], then #c[$Q_1$] contains no linear assumptions.
]

Proofs of these lemmas (and others) appear in Appendix B; they can be proved by straightforward use of the properties in Figure 4.

== Typing Rules
<sec:typing-rules>

With this material in place, we can now present our type system. The grammar is given in Figure 5, which also includes the definitions of scaling on contexts $pi cscale Gamma$ and addition of contexts $Gamma_1 + Gamma_2$. Note that addition on contexts is actually a partial function, as it requires that, if a variable $x$ is bound in both $Gamma_1$ and $Gamma_2$, then $x$ is assigned the same type in both (but perhaps different multiplicities). This partiality is not a problem in practice, as the required condition for combining contexts is always satisfied.

#v(0.5em)
#align(center)[
  #block(
    fill: rgb("fafafa"),
    inset: 1em,
    stroke: 0.5pt + luma(200),
    radius: 3pt,
  )[
    #align(left)[
      *Figure 5: Grammar of the qualified type system*
      #v(0.5em)
      $
        a, b &quad text("Type vars") quad quad x, y quad text("Expression vars") quad quad T quad text("Type constructors") quad quad K quad text("Data constructors") \
        sigma &::= forall overline(a). #c[$Q$] Lolly tau quad text("Type schemes") \
        tau, upsilon &::= a mid(|) ∃ overline(a). tau RLolly #c[$Q$] mid(|) tau_1 ->_pi tau_2 mid(|) T space overline(tau) quad text("Types") \
        Gamma, Delta &::= • mid(|) Gamma, x :_pi sigma quad text("Contexts") \
        e &::= x mid(|) K mid(|) lambda x. e mid(|) e_1 space e_2 mid(|) packbox space e mid(|) bold("let") space packbox space x = e_1 space bold("in") space e_2 \
        &mid(|) bold("case")_pi space e space bold("of") { overline(K_i space overline(x_i) -> e_i) } mid(|) bold("let")_pi space x = e_1 space bold("in") space e_2 mid(|) bold("let")_pi space x : sigma = e_1 space bold("in") space e_2
      $

      #v(0.5em)
      *Context scaling $pi cscale Gamma$ and addition of contexts $Gamma_1 + Gamma_2$ are defined as follows:*
      $
        cases(
          pi cscale • = •,
          pi cscale (Gamma, x :_rho sigma) = pi cscale Gamma #math.comma x :_(pi cscale rho) sigma,
        )
        quad quad
        cases(
          (Gamma_1, x :_pi sigma) + Gamma_2 = Gamma_1 + Gamma'_2 #math.comma x :_(pi + rho) sigma quad text("where") Gamma_2 = {x :_rho sigma} union Gamma'_2 #math.comma x in.not Gamma'_2,
          (Gamma_1, x :_pi sigma) + Gamma_2 = Gamma_1 + Gamma_2 #math.comma x :_pi sigma quad text("where") x in.not Gamma_2,
          • + Gamma_2 = Gamma_2,
        )
      $
    ]
  ]
]
#v(0.5em)

#block(
  fill: rgb("fafafa"),
  inset: 1em,
  stroke: 0.5pt + luma(200),
  radius: 3pt,
)[
  #align(center)[*Figure 6: Qualified type system* (#c[$Q$] $; Gamma ⊢ e : tau$)]

  #v(0.5em)
  #prooftree(rule(
    name: [E_Var],
    $Gamma_1 = x :_1 forall overline(a). #c[$Q_1$] Lolly upsilon$,
    $#c[$Q_1 [overline(tau) / overline(a)]$] ; Gamma_1 + omega cscale Gamma_2 ⊢ x : upsilon [overline(tau) / overline(a)]$,
  ))

  #v(0.8em)
  #prooftree(rule(
    name: [E_Abs],
    $#c[$Q$] ; Gamma, x :_pi tau_1 ⊢ e : tau_2$,
    $#c[$Q$] ; Gamma ⊢ lambda x. e : tau_1 ->_pi tau_2$,
  ))

  #v(0.8em)
  #prooftree(rule(
    name: [E_App],
    $#c[$Q_1$] ; Gamma_1 ⊢ e_1 : tau_1 ->_pi tau$,
    $#c[$Q_2$] ; Gamma_2 ⊢ e_2 : tau_1$,
    $#c[$Q_1 qtensor pi cscale Q_2$] ; Gamma_1 + pi cscale Gamma_2 ⊢ e_1 space e_2 : tau$,
  ))

  #v(0.8em)
  #prooftree(rule(
    name: [E_Pack],
    $#c[$Q$] ; Gamma ⊢ e : tau [overline(upsilon) / overline(a)]$,
    $#c[$Q qtensor Q_1 [overline(upsilon) / overline(a)]$] ; Gamma ⊢ packbox space e : ∃ overline(a). tau RLolly #c[$Q_1$]$,
  ))

  #v(0.8em)
  #prooftree(rule(
    name: [E_Unpack],
    $#c[$Q_1$] ; Gamma_1 ⊢ e_1 : ∃ overline(a). tau_1 RLolly #c[$Q$]$,
    $overline(a) text(" fresh")$,
    $#c[$Q_2 qtensor Q$] ; Gamma_2, x :_1 tau_1 ⊢ e_2 : tau$,
    $#c[$Q_1 qtensor Q_2$] ; Gamma_1 + Gamma_2 ⊢ bold("let") space packbox space x = e_1 space bold("in") space e_2 : tau$,
  ))

  #v(0.8em)
  #prooftree(rule(
    name: [E_Let],
    $#c[$Q_1 qtensor Q$] ; Gamma_1 ⊢ e_1 : tau_1$,
    $#c[$Q_2$] ; Gamma_2, x :_pi #c[$Q$] Lolly tau_1 ⊢ e_2 : tau$,
    $#c[$pi cscale Q_1 qtensor Q_2$] ; pi cscale Gamma_1 + Gamma_2 ⊢ bold("let")_pi space x = e_1 space bold("in") space e_2 : tau$,
  ))

  #v(0.8em)
  #prooftree(rule(
    name: [E_LetSig],
    $#c[$Q_1 qtensor Q$] ; Gamma_1 ⊢ e_1 : tau_1$,
    $overline(a) text(" fresh")$,
    $sigma = forall overline(a). #c[$Q$] Lolly tau_1$,
    $#c[$Q_2$] ; Gamma_2, x :_pi forall overline(a). #c[$Q$] Lolly tau_1 ⊢ e_2 : tau$,
    $#c[$pi cscale Q_1 qtensor Q_2$] ; pi cscale Gamma_1 + Gamma_2 ⊢ bold("let")_pi space x : sigma = e_1 space bold("in") space e_2 : tau$,
  ))

  #v(0.8em)
  #prooftree(rule(
    name: [E_Case],
    $#c[$Q_1$] ; Gamma_1 ⊢ e : T space overline(tau)$,
    $K_i : forall overline(a). overline(upsilon)_i ->_(overline(pi)_i) T space overline(a)$,
    $#c[$Q_2$] ; Gamma_2, overline(x_i :_((pi cscale pi_i)) upsilon_i [overline(tau) / overline(a)]) ⊢ e_i : tau$,
    $#c[$pi cscale Q_1 qtensor Q_2$] ; pi cscale Gamma_1 + Gamma_2 ⊢ bold("case")_pi space e space bold("of") { overline(K_i space overline(x_i) -> e_i) } : tau$,
  ))

  #v(0.8em)
  #prooftree(rule(
    name: [E_Sub],
    $#c[$Q_1$] ; Gamma ⊢ e : tau$,
    $#c[$Q$] ⊩ #c[$Q_1$]$,
    $#c[$Q$] ; Gamma ⊢ e : tau$,
  ))
]

The typing rules are in Figure 6. A qualified type system [Jones 1994] such as ours introduces a judgement of the form #c[$Q$] $; Gamma ⊢ e : tau$, where $Gamma$ is a standard type context, and #c[$Q$] is a constraint we have assumed to be true. #c[$Q$] behaves much like $Gamma$, which will be instrumental for desugaring in Section 7; the main difference is that $Gamma$ is addressed explicitly, whereas #c[$Q$] is used implicitly in rule `E_Var`.

Because constraints are used implicitly, if there are several instances of the same #c[$1 cscale q$], it is non-deterministic which one is used in which instance of `E_Var`. As a consequence, we must require that any two instances of #c[$1 cscale q$] in a constraint #c[$Q$] have the same computational content (see Section 7). How do we reconcile this non-determinism with the use of linear constraints, in Section 4.2 to thread mutations? We certainly don't want type inference to non-deterministically reorder a `readRef` and a `writeRef`! The solution is that the API is arranged so that only a single instance of #c[`RW n`] is ever provided. Therefore there is a single possible threading of the reads and writes. In contrast there will often be several instances of #c[`Linearly`] in scope.

The type system of Figure 6 is purely declarative: note, for example, that rule `E_App` does not describe how to break the typing assumptions into constraints #c[$Q_1$]/#c[$Q_2$] and contexts $Gamma_1$/$Gamma_2$. We will see how to infer constraints in Section 6. Yet, this system is our ground truth: a system with a simple enough definition that programmers can reason about typing. As is standard in the qualified-type literature (since the original paper [Jones 1994]), we do not directly give a dynamic semantics to this language; instead, we will give it meaning via desugaring to a simpler core language in Section 7.

We survey several distinctive features of our qualified type system below:

*Linear functions.* The type of linear functions is written $a ->_1 b$. Despite our focus on linear constraints, we still need linearity in ordinary arguments. Indeed, the linearity of arrows interacts in interesting ways with linear constraints: If $f : a ->_omega b$ and $x : #c[$1 cscale q$] =⚬ a$, then calling $f space x$ would actually use $q$ many times. We must make sure it is impossible to derive #c[$1 cscale q$] $; f : a ->_omega b, x : #c[$1 cscale q$] =⚬ a ⊢ f space x : b$. Otherwise we could make, for instance, the `overusing` function from @sec:overusing. You can check that #c[$1 cscale q$] $; f : a ->_omega b, x : #c[$1 cscale q$] =⚬ a ⊢ f space x : b$ indeed does not type check, because the scaling of #c[$Q_2$] in rule `E_App` ensures that the constraint would be #c[$omega cscale q$] instead. On the other hand, it is perfectly fine to have #c[$1 cscale q$] $; f : a ->_1 b, x : #c[$1 cscale q$] =⚬ a ⊢ f space x : b$ when $f$ is a linear function.

*Variables.* As is standard, the rule `E_Var` works in a context containing more than just the used binding for $x$. However, crucially, our rule allows only unrestricted variables to be discarded; linear variables must be used. We can see this in the rule by noticing that the context has an unrestricted component $omega cscale Gamma_2$. The $Gamma_1$ component might be restricted or might not, allowing this rule to apply both for restricted and unrestricted $x$.

*Data constructors.* Data constructors $K$ don't have a dedicated typing rule. Instead they are typed using the rule `E_Var`, where they are treated as if they were unrestricted variables.

*Let-bindings.* Bindings in a let may be for either linear or unrestricted variables. We could require all bindings to be linear and to implement unrestricted information only using `Ur`, but it is very easy to add a multiplicity annotation on let, and so we do.

*Local assumptions.* Rule `E_Let` includes support for local assumptions. We thus have the ability to generalise a subset of the constraints needed by $e_1$ (but not the type variables—no let-generalisation here, though it could be added). The inference algorithm of Section 6 will not make use of this possibility.

*Existentials.* We include $∃ overline(a). tau #RLolly #c[$Q$]$, as introduced in Section 3, together with the $packbox$ constructor. See rules `E_Pack` and `E_Unpack`.
= Constraint Inference
<sec:type-inference>

The type system of Figure 6 gives a declarative description of what programs are acceptable. We now present the algorithmic counterpart to this system. Our algorithm is structured, unsurprisingly, around generating and solving constraints, broadly following the template of Pottier and Rémy [2005]. That is, our algorithm takes a pass over the abstract syntax entered by the user, generating constraints as it goes. Then, separately, we solve those constraints (that is, try to satisfy them) in the presence of a set of assumptions, or we determine that the assumptions do not imply that the constraints hold. In the latter case, we issue an error to the programmer.

The procedure is responsible for inferring both types and constraints. For our type system, type inference can be done independently from constraint inference. Indeed, we focus on the latter, and defer type inference to an external oracle (such as [Matsuda 2020]). That is, we assume an algorithm that produces typing derivations for the judgement $Gamma ⊢ e : tau$, ignoring all the constraints. Then, we describe a constraint generation algorithm that passes over these typing derivations. We can make this simplification for two reasons:
- We do not formalise type equality constraints, and our implementation in GHC (@sec:equality-constraints) takes care to not allow linear equality constraints to influence type inference. Indeed, a typical treatment of unification would be unsound for linear equalities, because it reuses the same equality many times (or none at all). Linear equalities make sense (Shulman [2018] puts linear equalities to great use), but they do not seem to lend themselves to automation.
- We do not support, or intend to support, multiplicity polymorphism in constraint arrows. That is, the multiplicity of a constraint is always syntactically known to be either linear or unrestricted. This way, no equality constraints (which might, conceivably, relate multiplicity variables) can interfere with constraint resolution.

== Wanted Constraints
<sec:wanteds>

The constraints #c[$C$] generated in our system have a richer logical structure than the simple constraints #c[$Q$], above. Following GHC and echoing Vytiniotis, Peyton Jones, Schrijvers, and Sulzmann [2011], we call these _wanted constraints_: they are constraints which the constraint solver wants to prove. An unproved wanted constraint results in a type error reported to the programmer.

$
  #c[$C$] &::= #c[$Q$] mid(|) #c[$C_1 qtensor C_2$] mid(|) #c[$C_1 aand C_2$] mid(|) #c[$pi cscale (Q Lolly C)$] quad text("Wanted constraints")
$

A simple constraint is a valid wanted constraint, and we have two forms of conjunction for wanted constraints: the new #c[$C_1 aand C_2$] construction (read $C_1$ _with_ $C_2$), alongside the more typical #c[$C_1 qtensor C_2$]. These are connectives from linear logic: #c[$C_1 qtensor C_2$] is the multiplicative conjunction, and #c[$C_1 aand C_2$] is the additive conjunction. Both connectives are conjunctions, but they differ in meaning. To satisfy #c[$C_1 qtensor C_2$] one consumes the (linear) assumptions consumed by satisfying #c[$C_1$] and those consumed by #c[$C_2$]; if an assumed linear constraint is needed to prove both #c[$C_1$] and #c[$C_2$], then #c[$C_1 qtensor C_2$] will not be provable, because that linear assumption cannot be used twice. On the other hand, satisfying #c[$C_1 aand C_2$] requires that satisfying #c[$C_1$] and #c[$C_2$] must each consume the same assumptions, which #c[$C_1 aand C_2$] consumes as well. Thus, if #c[$C$] is assumed linearly (and we have no other assumptions), then #c[$C qtensor C$] is not provable, while #c[$C aand C$] is. The intuition, here, is that in #c[$C_1 aand C_2$], only one of #c[$C_1$] or #c[$C_2$] will be eventually used. "With" constraints arise from the branches in a case-expression.

The last form of wanted constraint #c[$C$] is an implication #c[$pi cscale (Q Lolly C)$]. The more interesting case is #c[$omega cscale (Q Lolly C)$]: to prove #c[$omega cscale (Q Lolly C)$], you need to prove #c[$C$] under the linear assumption #c[$Q$], but without using any other linear assumptions.

These implications arise when we unpack an existential package that contains a linear constraint and also when checking a let-binding. We can define scaling over wanted constraints by recursion as follows, where we use scaling over simple constraints in the simple-constraint case:
$
  cases(
    #c[$pi cscale (C_1 qtensor C_2)$] = #c[$pi cscale C_1 qtensor pi cscale C_2$],
    #c[$1 cscale (C_1 aand C_2)$] = #c[$C_1 aand C_2$],
    #c[$omega cscale (C_1 aand C_2)$] = #c[$omega cscale C_1 qtensor omega cscale C_2$],
    #c[$pi cscale (rho cscale (Q Lolly C))$] = #c[$(pi cscale rho) cscale (Q Lolly C)$],
  )
$

For the most part, scaling of wanted constraints is straightforward. The only peculiar case is when we scale the additive conjunction #c[$C_1 aand C_2$] by $omega$, the result is a multiplicative conjunction. The intuition here is that if we have both #c[$omega cscale C_1$] and #c[$omega cscale C_2$], then a choice between #c[$C_1$] and #c[$C_2$] can be made $omega$ times.

We define an entailment relation over wanteds in Figure 7. Note that this relation uses only simple constraints #c[$Q$] as assumptions, as there is no way to assume the more elaborate #c[$C$].

#v(0.5em)
#align(center)[
  #block(
    fill: rgb("fafafa"),
    inset: 1em,
    stroke: 0.5pt + luma(200),
    radius: 3pt,
  )[
    #align(center)[*Figure 7: Wanted-constraint entailment* (#c[$Q$] $⊢$ #c[$C$])]

    #v(0.5em)
    #grid(
      columns: (1fr, 1fr),
      gutter: 1.5em,
      align: center + horizon,
      prooftree(rule(
        name: [C_Dom],
        $#c[$Q_1$] ⊩ #c[$Q_2$]$,
        $#c[$Q_2$] ⊢ #c[$Q_3$]$,
        $#c[$Q_1$] ⊢ #c[$Q_3$]$,
      )),
      prooftree(rule(
        name: [C_Id],
        $#c[$Q$] ⊢ #c[$Q$]$,
      )),
    )

    #v(0.8em)
    #grid(
      columns: (1.2fr, 1fr),
      gutter: 1.5em,
      align: center + horizon,
      prooftree(rule(
        name: [C_Tensor],
        $#c[$Q_1$] ⊢ #c[$C_1$]$,
        $#c[$Q_2$] ⊢ #c[$C_2$]$,
        $#c[$Q_1 qtensor Q_2$] ⊢ #c[$C_1 qtensor C_2$]$,
      )),
      prooftree(rule(
        name: [C_With],
        $#c[$Q$] ⊢ #c[$C_1$]$,
        $#c[$Q$] ⊢ #c[$C_2$]$,
        $#c[$Q$] ⊢ #c[$C_1 aand C_2$]$,
      )),
    )

    #v(0.8em)
    #prooftree(rule(
      name: [C_Impl],
      $#c[$Q_0 qtensor Q_1$] ⊢ #c[$C$]$,
      $#c[$pi cscale Q_0$] ⊢ #c[$pi cscale (Q_1 Lolly C)$]$,
    ))
  ]
]
#v(0.5em)

Before we move on to constraint generation proper, let us highlight a few technical, yet essential, lemmas about the wanted-constraint entailment relation.

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Lemma 6.1 (Inversion).*
  The inference rules of #c[$Q$] $⊢$ #c[$C$] can be read bottom-up (up to the set #c[$cal(D)$]) as well as top-down, as is required of #c[$Q_1$] $⊩$ #c[$Q_2$] in Figure 4. That is:
  - If #c[$Q$] $⊢$ #c[$C_1 qtensor C_2$], then there exist #c[$Q_1$], #c[$Q_cal(D)$] and #c[$Q_2$] such that #c[$Q_cal(D) in cal(D)$], #c[$Q_1 qtensor Q_cal(D)$] $⊢$ #c[$C_1$], #c[$Q_cal(D) qtensor Q_2$] $⊢$ #c[$C_2$], and #c[$Q$] $= #c[$Q_1 qtensor Q_cal(D) qtensor Q_2$]$.
  - If #c[$Q$] $⊢$ #c[$C_1 aand C_2$], then #c[$Q$] $⊢$ #c[$C_1$] and #c[$Q$] $⊢$ #c[$C_2$].
  - If #c[$Q$] $⊢$ #c[$pi cscale (Q_2 Lolly C)$], then there exists #c[$Q_1$] such that #c[$Q_1 qtensor Q_2$] $⊢$ #c[$C$] and #c[$Q$] $= #c[$pi cscale Q_1$]$.
]

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Lemma 6.2 (Scaling).* If #c[$Q$] $⊢$ #c[$C$], then #c[$pi cscale Q$] $⊢$ #c[$pi cscale C$].
]

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Lemma 6.3 (Inversion of scaling).* If #c[$Q$] $⊢$ #c[$pi cscale C$], then #c[$Q'$] $⊢$ #c[$C$] and #c[$Q$] $= #c[$pi cscale Q'$]$ for some #c[$Q'$].
]

== Constraint Generation
<sec:constraint-generation>

The process of inferring constraints is split into two parts: generating constraints, which we do in this section, then solving them in @sec:constraint-solver. Constraint generation is described by the judgement $Gamma vdashi e : tau leadsto$ #c[$C$] (defined in Figure 8) which outputs a constraint #c[$C$] required to make $e$ typecheck.

The definition $Gamma vdashi e : tau leadsto$ #c[$C$] is syntax directed, so it can directly be read as an algorithm, taking as input a typing derivation for $Gamma ⊢ e : tau$ (produced by an external type inference oracle as discussed above). Notably, the algorithm has access to the context splitting from the (previously computed) typing derivation, and is thus indeed syntax directed.

The rules of Figure 8 constitute a mostly unsurprising translation of the rules of Figure 6, except for the following points of interest:

- *Case expressions.* Note the use of #c[$aand$] in the conclusion of rule `G_Case`. We require that each branch of a case expression use the exact same (linear) assumptions; this is enforced by combining the emitted constraints with #c[$aand$], not #c[$qtensor$]. This can also be understood in terms of the array example of Section 1: if an array is freed in one branch of a case, we require it to be freed (or freezed) in the other branches too. Otherwise, the array's state will be unknown to the type system after the case.
- *Implications.* The introduction of constraints local to a definition (rule `G_LetSig`) corresponds to emitting an implication constraint.
- *Unannotated let.* However, the `G_Let` rule does not produce an implication constraint, as we do not model let-generalisation [Vytiniotis, Peyton Jones, and Schrijvers 2010].

#v(0.5em)
#align(center)[
  #block(
    fill: rgb("fafafa"),
    inset: 1em,
    stroke: 0.5pt + luma(200),
    radius: 3pt,
  )[
    #align(center)[*Figure 8: Constraint generation* ($Gamma vdashi e : tau leadsto$ #c[$C$])]

    #v(0.5em)
    #prooftree(rule(
      name: [G_Var],
      $Gamma_1 = x :_1 forall overline(a). #c[$Q$] Lolly upsilon$,
      $Gamma_1 + omega cscale Gamma_2 vdashi x : upsilon [overline(tau) / overline(a)] leadsto #c[$Q [overline(tau) / overline(a)]$]$,
    ))

    #v(0.8em)
    #prooftree(rule(
      name: [G_Abs],
      $Gamma, x :_pi tau_0 vdashi e : tau leadsto #c[$C$]$,
      $Gamma vdashi lambda x. e : tau_0 ->_pi tau leadsto #c[$C$]$,
    ))

    #v(0.8em)
    #prooftree(rule(
      name: [G_App],
      $Gamma_1 vdashi e_1 : tau_2 ->_pi tau leadsto #c[$C_1$]$,
      $Gamma_2 vdashi e_2 : tau_2 leadsto #c[$C_2$]$,
      $Gamma_1 + pi cscale Gamma_2 vdashi e_1 space e_2 : tau leadsto #c[$C_1 qtensor pi cscale C_2$]$,
    ))

    #v(0.8em)
    #prooftree(rule(
      name: [G_Pack],
      $Gamma vdashi e : tau [overline(upsilon) / overline(a)] leadsto #c[$C$]$,
      $Gamma vdashi packbox space e : ∃ overline(a). tau RLolly #c[$Q$] leadsto #c[$C qtensor Q [overline(upsilon) / overline(a)]$]$,
    ))

    #v(0.8em)
    #prooftree(rule(
      name: [G_Unpack],
      $Gamma_1 vdashi e_1 : ∃ overline(a). tau_1 RLolly #c[$Q_1$] leadsto #c[$C_1$]$,
      $overline(a) text(" fresh")$,
      $Gamma_2, x :_1 tau_1 vdashi e_2 : tau leadsto #c[$C_2$]$,
      $Gamma_1 + Gamma_2 vdashi bold("let") space packbox space x = e_1 space bold("in") space e_2 : tau leadsto #c[$C_1 qtensor 1 cscale (Q_1 Lolly C_2)$]$,
    ))

    #v(0.8em)
    #prooftree(rule(
      name: [G_Case],
      $Gamma vdashi e : T space overline(sigma) leadsto #c[$C$]$,
      $K_i : forall overline(a). overline(upsilon)_i ->_(overline(pi)_i) T space overline(a)$,
      $Delta, overline(x_i :_((pi cscale pi_i)) upsilon_i [overline(sigma) / overline(a)]) vdashi e_i : tau leadsto #c[$C_i$]$,
      $pi cscale Gamma + Delta vdashi bold("case")_pi space e space bold("of") { overline(K_i space overline(x_i) -> e_i) } : tau leadsto #c[$pi cscale C qtensor bigaand C_i$]$,
    ))

    #v(0.8em)
    #prooftree(rule(
      name: [G_Let],
      $Gamma_1 vdashi e_1 : tau_1 leadsto #c[$C_1$]$,
      $Gamma_2, x :_pi tau_1 vdashi e_2 : tau leadsto #c[$C_2$]$,
      $pi cscale Gamma_1 + Gamma_2 vdashi bold("let")_pi space x = e_1 space bold("in") space e_2 : tau leadsto #c[$pi cscale C_1 qtensor C_2$]$,
    ))

    #v(0.8em)
    #prooftree(rule(
      name: [G_LetSig],
      $Gamma_1 vdashi e_1 : tau_1 leadsto #c[$C_1$]$,
      $overline(a) text(" fresh")$,
      $Gamma_2, x :_pi forall overline(a). #c[$Q$] Lolly tau_1 vdashi e_2 : tau leadsto #c[$C_2$]$,
      $pi cscale Gamma_1 + Gamma_2 vdashi bold("let")_pi space x : forall overline(a). #c[$Q$] Lolly tau_1 = e_1 space bold("in") space e_2 : tau leadsto #c[$C_2 qtensor pi cscale (Q Lolly C_1)$]$,
    ))
  ]
]
#v(0.5em)

The key property of the constraint-generation algorithm is that, if the generated constraint is solvable, then we can indeed type the term in the qualified type system of Section 5. That is, these rules are simply an implementation of our declarative qualified type system.

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Lemma 6.4 (Soundness of constraint generation).*
  For all #c[$Q_g$], if $Gamma vdashi e : tau leadsto$ #c[$C$] and #c[$Q_g$] $⊢$ #c[$C$], then #c[$Q_g$] $; Gamma ⊢ e : tau$.
]

== Constraint Solving
<sec:constraint-solver>

In this section, we build a constraint solver that proves that #c[$Q_g$] $⊢$ #c[$C$] holds, as required by Lemma 6.4. The constraint solver is represented by the following judgement:
$ #c[$U$] ; #c[$D$] ; #c[$L_i$] vdashs #c[$C$] leadsto #c[$L_o$] $

The judgement takes in three contexts: #c[$U$], which holds all the unrestricted atomic constraint assumptions, #c[$D$] which holds the linear atomic assumptions which are members of #c[$cal(D)$], and #c[$L_i$], which holds the linear atomic constraint assumptions which aren't members of #c[$cal(D)$]. The linear contexts #c[$D$], #c[$L_i$], and #c[$L_o$] have been described as multisets (@sec:constraint-domain), but we treat them as ordered lists in the more concrete setting here; we will see soon why this treatment is necessary.

Linearity requires treating constraints as consumable resources. This is what #c[$L_o$] is for: it contains the hypotheses of #c[$L_i$] which are not consumed when proving #c[$C$]. As suggested by the notation, it is an output of the algorithm. Constraints from #c[$D$] are never outputted in #c[$L_i$]: if constraints from #c[$D$] remain unused, we weaken them instead.

If the constraint solver finds a solution, then the output linear constraints must be a subset of the input linear constraints, and the solution must indeed be entailed from the given assumptions.

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Lemma 6.5 (Constraint solver soundness).*
  If #c[$U$] $;$ #c[$D$] $;$ #c[$L_i$] $vdashs$ #c[$C$] $leadsto$ #c[$L_o$], then:
  1. #c[$L_o$] $subset.eq$ #c[$L_i$]
  2. #c[$(U, D uplus L_i)$] $⊢$ #c[$C qtensor (emptyset, L_o)$]
]

To handle simple wanted constraints, we will need a domain-specific atomic-constraint solver to be the algorithmic counterpart of the abstract entailment relation of @sec:constraint-domain. The main solver will appeal to this atomic-constraint solver when solving atomic constraints. The atomic-constraint solver is represented by the following judgement:
$ #c[$U$] ; #c[$D$] ; #c[$L_i$] vdashsimp #c[$pi cscale q$] leadsto #c[$L_o$] $

It has a similar structure to the main solver, but only deals with atomic constraints. Even though the main solver is parameterised by this atomic-constraint solver, we will give an instantiation in @sec:simple-constr-solv. We require the following property of the atomic-constraint solver:

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Property 6.6 (Atomic-constraint solver soundness).*
  If #c[$U$] $;$ #c[$D$] $;$ #c[$L_i$] $vdashsimp$ #c[$pi cscale q$] $leadsto$ #c[$L_o$], then:
  1. #c[$L_o$] $subset.eq$ #c[$L_i$]
  2. #c[$(U, D uplus L_i)$] $⊩$ #c[$pi cscale q qtensor (emptyset, L_o)$]
]

=== Constraint Solver Algorithm
<sec:solver-algorithm>

Building on this atomic-constraint solver, we use a linear proof search algorithm based on the recipe given by Cervesato et al. [2000]. Figure 9 presents the rules of the constraint solver:

- The `S_Mult` rule proceeds by solving one side of a conjunction first, then passing the output constraints to the other side. Both the unrestricted context and the duplicable context are shared between both sides.
- The `S_Add` rule handles additive conjunction. The linear constraints are shared between the branches (since additive conjunction is generated from case expressions, only one of them is actually going to be executed). Both branches must consume exactly the same resources.
- The `S_ImplOne` rule handles linear implications. The unrestricted and linear components of the assumption are unioned with their respective context when solving the conclusion. Note how the linear constraints, in particular, are classified according to whether they are members of #c[$cal(D)$] or not. Importantly (see @sec:simple-constr-solv), the linear assumptions are added to the front of the lists. The side condition that the output context is a subset of the input context ensures that the implication fully consumes its assumption and does not leak it to the ambient context.
- The `S_ImplMany` rule handles unrestricted implication. The conclusion uses its own linear assumption, but none of the other linear constraints. This is because, as per `C_Impl`, unrestricted implications can only use an unrestricted context. In particular, crucially, the constraints from #c[$cal(D)$], despite being duplicable and discardable, are not (and cannot) be used to prove an unrestricted implication, as first discussed in @sec:constraint-domain.

#v(0.5em)
#align(center)[
  #block(
    fill: rgb("fafafa"),
    inset: 1em,
    stroke: 0.5pt + luma(200),
    radius: 3pt,
  )[
    #align(
      center,
    )[*Figure 9: Constraint solver* (#c[$U$] $;$ #c[$D$] $;$ #c[$L_i$] $vdashs$ #c[$C_w$] $leadsto$ #c[$L_o$])]

    #v(0.5em)
    #prooftree(rule(
      name: [S_Atom],
      $#c[$U$] ; #c[$D$] ; #c[$L_i$] vdashsimp #c[$pi cscale q$] leadsto #c[$L_o$]$,
      $#c[$U$] ; #c[$D$] ; #c[$L_i$] vdashs #c[$pi cscale q$] leadsto #c[$L_o$]$,
    ))

    #v(0.8em)
    #prooftree(rule(
      name: [S_Mult],
      $#c[$U$] ; #c[$D$] ; #c[$L_i$] vdashs #c[$C_1$] leadsto #c[$L'_o$]$,
      $#c[$U$] ; #c[$D$] ; #c[$L'_o$] vdashs #c[$C_2$] leadsto #c[$L_o$]$,
      $#c[$U$] ; #c[$D$] ; #c[$L_i$] vdashs #c[$C_1 qtensor C_2$] leadsto #c[$L_o$]$,
    ))

    #v(0.8em)
    #prooftree(rule(
      name: [S_Add],
      $#c[$U$] ; #c[$D$] ; #c[$L_i$] vdashs #c[$C_1$] leadsto #c[$L_o$]$,
      $#c[$U$] ; #c[$D$] ; #c[$L_i$] vdashs #c[$C_2$] leadsto #c[$L_o$]$,
      $#c[$U$] ; #c[$D$] ; #c[$L_i$] vdashs #c[$C_1 aand C_2$] leadsto #c[$L_o$]$,
    ))

    #v(0.8em)
    #prooftree(rule(
      name: [S_ImplOne],
      $#c[$U union U_0$] ; #c[$D uplus (L_0 inter cal(D))$] ; #c[$L_i uplus (L_0 backslash cal(D))$] vdashs #c[$C$] leadsto #c[$L_o$]$,
      $#c[$L_o$] subset.eq #c[$L_i$]$,
      $#c[$U$] ; #c[$D$] ; #c[$L_i$] vdashs #c[$1 cscale ((U_0, L_0) Lolly C)$] leadsto #c[$L_o$]$,
    ))

    #v(0.8em)
    #prooftree(rule(
      name: [S_ImplMany],
      $#c[$U union U_0$] ; #c[$L_0 inter cal(D)$] ; #c[$L_0 backslash cal(D)$] vdashs #c[$C$] leadsto #c[$emptyset$]$,
      $#c[$U$] ; #c[$D$] ; #c[$L_i$] vdashs #c[$omega cscale ((U_0, L_0) Lolly C)$] leadsto #c[$L_i$]$,
    ))
  ]
]

=== An Atomic-Constraint Solver
<sec:simple-constr-solv>

So far, the atomic-constraint domain has been an abstract parameter. In this section, though, we offer a concrete domain which supports our examples.

For the sake of our examples, we need very little: linear constraints can remain abstract. It is thus sufficient for the entailment relation (Figure 10a) to prove $q$ if and only if it is already assumed—while respecting linearity. That is, with the exception of a distinguished constraint #c[$cal(L)$], which can be duplicated and discarded, and we use to model the #c[`Linearly`] constraint from @sec:Unique-constraint. The set #c[$cal(D)$] is defined to only contain #c[$cal(L)$], therefore the #c[$D$] context is a sequence of 0 or more #c[$cal(L)$].

#v(0.5em)
#align(center)[
  #block(
    fill: rgb("fafafa"),
    inset: 1em,
    stroke: 0.5pt + luma(200),
    radius: 3pt,
  )[
    #align(center)[*(a) Entailment Relation:* #c[$Q_1$] $⊩$ #c[$Q_2$]]

    #v(0.5em)
    #grid(
      columns: (1.2fr, 1fr),
      gutter: 1.5em,
      align: center + horizon,
      prooftree(rule(
        name: [Q_Hyp],
        $#c[$omega cscale Q qtensor pi cscale q$] ⊩ #c[$pi cscale q$]$,
      )),
      prooftree(rule(
        name: [Q_Empty],
        $#c[$omega cscale Q$] ⊩ ceps$,
      )),
    )

    #v(0.8em)
    #grid(
      columns: (1.2fr, 1fr),
      gutter: 1.5em,
      align: center + horizon,
      prooftree(rule(
        name: [Q_Prod],
        $#c[$Q_1$] ⊩ #c[$Q'_1$]$,
        $#c[$Q_2$] ⊩ #c[$Q'_2$]$,
        $#c[$Q_1 qtensor Q_2$] ⊩ #c[$Q'_1 qtensor Q'_2$]$,
      )),
      prooftree(rule(
        name: [Q_DiscardD],
        $#c[$1 cscale cal(L)$] ⊩ ceps$,
      )),
    )

    #v(0.8em)
    #prooftree(rule(
      name: [Q_DupD],
      $#c[$1 cscale cal(L)$] ⊩ #c[$1 cscale cal(L) qtensor 1 cscale cal(L)$]$,
    ))
  ]
]

The corresponding atomic-constraint solver (Figure 10b) is more interesting. It is deterministic: in all circumstances, only one of the three rules can apply. This means that the algorithm does not guess, thus never needs to backtrack. Avoiding guesses is a key property of GHC's solver [Vytiniotis, Peyton Jones, Schrijvers, and Sulzmann 2011, Section 6.4], one we must maintain if we are to be compatible with GHC.

#v(0.5em)
#align(center)[
  #block(
    fill: rgb("fafafa"),
    inset: 1em,
    stroke: 0.5pt + luma(200),
    radius: 3pt,
  )[
    #align(
      center,
    )[*(b) Atomic-Constraint Solver:* #c[$U$] $;$ #c[$D$] $;$ #c[$L$] $vdashsimp$ #c[$pi cscale q$] $leadsto$ #c[$L_o$]]

    #v(0.5em)
    #prooftree(rule(
      name: [Atom_Many],
      $#c[$q$] in #c[$U$]$,
      $#c[$U$] ; #c[$D$] ; #c[$L$] vdashsimp #c[$omega cscale q$] leadsto #c[$L$]$,
    ))

    #v(0.8em)
    #prooftree(rule(
      name: [Atom_OneL],
      $#c[$L$] = #c[$L_1, q, L_2$]$,
      $#c[$q$] in.not #c[$L_2$]$,
      $#c[$q$] in.not #c[$U$]$,
      $#c[$U$] ; #c[$D$] ; #c[$L$] vdashsimp #c[$1 cscale q$] leadsto #c[$L_1, L_2$]$,
    ))

    #v(0.8em)
    #prooftree(rule(
      name: [Atom_OneD],
      $#c[$cal(L)$] in.not #c[$U$]$,
      $#c[$U$] ; #c[$D, cal(L)$] ; #c[$L$] vdashsimp #c[$1 cscale q$] leadsto #c[$L$]$,
    ))

    #v(0.8em)
    #prooftree(rule(
      name: [Atom_OneU],
      $#c[$q$] in #c[$U$]$,
      $#c[$q$] in.not (#c[$D$] uplus #c[$L$])$,
      $#c[$U$] ; #c[$D$] ; #c[$L$] vdashsimp #c[$1 cscale q$] leadsto #c[$L$]$,
    ))
  ]
  *Figure 10: A stripped-down constraint domain*
]
#v(0.5em)

Figure 10b is also where the fact that the #c[$L$] are lists comes into play. Indeed, rule `Atom_OneL` takes care to use the most recent occurrence of #c[$q$] (remember that rule `S_ImplOne` adds the new hypotheses on the front of the list). To understand why, consider the following example:

```haskell
f = linearly $
  let □ (Ur arr) = new 10
      fr :: RW n =⚬ ()
      fr = free arr
      () = fr
  in Ur ()
```

In this example, the programmer meant for `free` to use the #c[`RW n`] constraint introduced locally in the type of `fr`. Yet there are actually two linear #c[`RW n`] constraints: this local one and the one assumed when unpacking `arr`. The wrong choice among the constraints will lead the algorithm to fail. Choosing the first #c[$q$] linear assumption guarantees we get the most local one.

Another interesting feature of the solver (Figure 10b) is that no rule solves a linear constraint if it appears both in the unrestricted and a linear context. Consider the following (contrived) API:

```haskell
class C
giveC :: (C => Int) -> Int
useC  :: C =⚬ Int
```

`giveC` gives an unrestricted copy of #c[`C`] to some continuation, while `useC` uses #c[`C`] linearly. Now consider two potential consumers of this API:

```haskell
ambiguous1 :: C =⚬ Int
ambiguous1 = giveC useC

ambiguous2 :: C =⚬ (Int, Int)
ambiguous2 = (giveC useC, useC)
```

Looking at `ambiguous1`, the invocation of `useC` has both a linear #c[`C`] in scope, and a more local unrestricted #c[`C`]. The strategy to pick the more local constraint fails here, because it would leave the linear #c[`C`] unconsumed. A tempting refinement might be to always consume the most local linear constraint. That would handle `ambiguous1` correctly, but fail on `ambiguous2`. In the case of the latter, if the invocation of `giveC useC` consumes the linear #c[`C`], then the second `useC` invocation will fail. It is possible to give a type derivation to `ambiguous2` in the qualified type system of Section 5 by making the first `useC` consume the unrestricted #c[`C`] and the second `useC` consume the linear #c[`C`]. This assignment, however, would require the constraint solver to guess when solving the constraint from the first `useC`. Accordingly, in order to both avoid backtracking and to keep type inference independent of the order terms appear in the program text, both are rejected. This introduces incompleteness with respect to the entailment relation. We conjecture that this is the only source of incompleteness that we introduce beyond what is already in GHC [Vytiniotis, Peyton Jones, Schrijvers, and Sulzmann 2011, Section 6].
= Desugaring
<sec:desugaring>

The semantics of our language is given by desugaring it into a simpler core language: a variant of the $lambda^q$ calculus [Bernardy et al. 2017]. We define the core language's type system here; its operational semantics is the same, _mutatis mutandis_, as that of Linear Haskell.

== The Core Calculus
<sec:core-calculus>

The core calculus is a variant of the type system defined in Section 5, but without constraints. That is, the evidence for constraints is passed explicitly in this core calculus. Following $lambda^q$, we assume the existence of the following data types:
- $tau_1 times.o tau_2$ with sole constructor $(,) : forall a space b. a ->_1 b ->_1 a times.o b$. We will write $(e_1, e_2)$ for $(,) space e_1 space e_2$.
- $bold(1)$ with sole constructor $() : bold(1)$.
- $mono("Ur") space tau$ with sole constructor $mono("Ur") : forall a. a ->_omega mono("Ur") space a$.

Figure 11 highlights the differences from the qualified system:
- Type schemes $sigma$ do not support qualified types.
- Existentially quantified types ($∃ overline(a). tau #RLolly #c[$Q$]$) are now represented as an (existentially quantified, linear) pair of values ($∃ overline(a). tau_2 times.o tau_1$). Accordingly, $packbox$ operates on pairs.

The differences between our core calculus and $lambda^q$ are as follows:
- We do not support multiplicity polymorphism.
- On the other hand, we do include type polymorphism.
- Polymorphism is implicit rather than explicit. This is not an essential difference, but it simplifies the presentation. We could, for example, include more details in the terms in order to make type-checking more obvious; this amounts essentially to an encoding of typing derivations in the terms.
- We have existential types. These can be realised in regular Haskell as a family of datatypes.

#v(0.5em)
#align(center)[
  #block(
    fill: rgb("fafafa"),
    inset: 1em,
    stroke: 0.5pt + luma(200),
    radius: 3pt,
  )[
    #align(center)[*Figure 11: Core calculus (subset)* ($Gamma ⊢ e : tau$)]
    #v(0.5em)
    $
      sigma &::= forall overline(a). tau quad text("Type schemes") \
      tau, upsilon &::= dots mid(|) ∃ overline(a). tau_2 times.o tau_1 quad text("Types") \
      e &::= dots mid(|) packbox space (e_1, e_2) mid(|) bold("let") space packbox (x, y) = e_1 space bold("in") space e_2 quad text("Expressions")
    $

    #v(0.8em)
    #prooftree(rule(
      name: [L_Pack],
      $Gamma_1 ⊢ e_1 : tau_1 [overline(upsilon) / overline(a)]$,
      $Gamma_2 ⊢ e_2 : tau_2 [overline(upsilon) / overline(a)]$,
      $Gamma_1 + Gamma_2 ⊢ packbox space (e_1, e_2) : ∃ overline(a). tau_2 times.o tau_1$,
    ))

    #v(0.8em)
    #prooftree(rule(
      name: [L_Unpack],
      $Gamma_1 ⊢ e_1 : ∃ overline(a). tau_2 times.o tau_1$,
      $overline(a) text(" fresh")$,
      $Gamma_2, x :_1 tau_1, y :_1 tau_2 ⊢ e_2 : tau$,
      $Gamma_1 + Gamma_2 ⊢ bold("let") space packbox (x, y) = e_1 space bold("in") space e_2 : tau$,
    ))
  ]
]
#v(0.5em)

Using Lemma 6.4 together with Lemma 6.5 we know that if $Gamma vdashi e : tau leadsto #c[$C$]$ and #c[$U$] $;$ #c[$D$] $;$ #c[$L$] $vdashs$ #c[$C$] $leadsto emptyset$, then #c[$(U, D uplus L)$] $; Gamma ⊢ e : tau$. It only remains to desugar derivations of #c[$Q$] $; Gamma ⊢ e : tau$ into the core calculus.

== From Qualified to Core
<sec:ds:from-qualified-core>

=== Evidence
<sec:ds:evidence>

In order to desugar derivations of the qualified system to the core calculus, we pass evidence explicitly. To do so, we require some more material from constraints. Namely, we assume a type $dsevidence(#c[$q$])$ for each atomic constraint #c[$q$], defined in Figure 12a. The $dsevidence(dots)$ operation extends to simple constraints as $dsevidence(#c[$Q$])$. Furthermore, we require that for every #c[$Q_1$] and #c[$Q_2$] such that #c[$Q_1$] $⊩$ #c[$Q_2$], there is a (linear) function:
$ dsevidence(#c[$Q_1$] ⊩ #c[$Q_2$]) :: dsevidence(#c[$Q_1$]) ->_1 dsevidence(#c[$Q_2$]) $

Let us now define a family of functions $dstype(dots)$ to translate the type schemes, types, contexts, and typing derivations of the qualified system into the types, type schemes, contexts, and terms of the core calculus.

=== Translating Types
<sec:ds:types>

Type schemes $sigma$ are translated by turning the implicit argument #c[$Q$] into an explicit one of type $dsevidence(#c[$Q$])$. Translating types $tau$ and contexts $Gamma$ proceeds as expected:

$
  cases(
    dstype(forall overline(a). #c[$Q$] Lolly tau) = forall overline(a). dsevidence(#c[$Q$]) ->_1 dstype(tau),
    dstype(tau_1 ->_pi tau_2) = dstype(tau_1) ->_pi dstype(tau_2),
    dstype(∃ overline(a). tau RLolly #c[$Q$]) = ∃ overline(a). dstype(tau) times.o dsevidence(#c[$Q$]),
  )
  quad quad
  cases(
    dstype(•) = •,
    dstype(Gamma, x :_pi tau) = dstype(Gamma), x :_pi dstype(tau),
  )
$

=== Translating Terms
<sec:ds:terms>

Given a derivation #c[$Q$] $; Gamma ⊢ e : tau$, we can build an expression $⟦ #c[$Q$] ; Gamma ⊢ e : tau ⟧_(z)$, such that $dstype(Gamma), z :_1 dsevidence(#c[$Q$]) ⊢ ⟦ #c[$Q$] ; Gamma ⊢ e : tau ⟧_(z) : dstype(tau)$ (for some fresh variable $z$). Even though we abbreviate the derivation as only its concluding judgement, the translation is defined recursively on the whole typing derivation: in particular, we have access to typing rule premises in the body of the definition. We present some of the interesting cases in Figure 12b.

The cases correspond to the `E_Var`, `E_Unpack`, and `E_Sub` rules, respectively. Variables are stored with qualified types in the environment, so they get translated to functions that take the evidence as argument. Accordingly, the evidence is inserted by passing $z$ as an argument. Handling `E_Unpack` requires splitting the context into two: $e_1$ is desugared as a pair, and the evidence it contains is passed to $e_2$. Finally, subsumption summons the function corresponding to the entailment relation #c[$Q$] $⊩$ #c[$Q_1$] and applies it to $z : dsevidence(#c[$Q$])$, then proceeds to desugar $e$ with the resulting evidence for #c[$Q_1$]. Crucially, since $⟦ dots ⟧_(z)$ is defined on derivations, we can access the premises used in the rule. Namely, #c[$Q_1$] is available in this last case from the `E_Sub` rule's premise.

#v(0.5em)
#align(center)[
  #block(
    fill: rgb("fafafa"),
    inset: 1em,
    stroke: 0.5pt + luma(200),
    radius: 3pt,
  )[
    #align(center)[*Figure 12: Evidence passing and desugaring*]
    #v(0.5em)
    #grid(
      columns: (1fr, 1.4fr),
      gutter: 1.5em,
      align: top + left,
      [
        *(a) Evidence passing*
        $
          cases(
            dsevidence(#c[$1 cscale q$]) = dsevidence(#c[$q$]),
            dsevidence(#c[$omega cscale q$]) = mono("Ur") space (dsevidence(#c[$q$])),
            dsevidence(ceps) = bold(1),
            dsevidence(#c[$Q_1 qtensor Q_2$]) = dsevidence(#c[$Q_1$]) times.o dsevidence(#c[$Q_2$]),
          )
        $
      ],
      [
        *(b) Desugaring (subset)*
        $
          ⟦ #c[$Q$] ; Gamma ⊢ x : upsilon [overline(tau) / overline(a)] ⟧_(z) &= x space z \
          ⟦ #c[$Q qtensor Q_1 [overline(upsilon) / overline(a)]$] ; Gamma ⊢ packbox space e : ∃ overline(a). tau RLolly #c[$Q_1$] ⟧_(z) &=
          bold("case")_1 space z space bold("of") { (z', z'') -> \
            &quad packbox space (z'', ⟦ #c[$Q$] ; Gamma ⊢ e : tau [overline(upsilon) / overline(a)] ⟧_(z')) } \
          ⟦ #c[$Q_1 qtensor Q_2$] ; Gamma_1 + Gamma_2 ⊢ bold("let") space packbox space x = e_1 space bold("in") space e_2 : tau ⟧_(z) &=
          bold("case")_1 space z space bold("of") { (z_1, z_2) -> \
            &quad bold("let") space packbox (z', x) = ⟦ #c[$Q_1$] ; Gamma_1 ⊢ e_1 : ∃ overline(a). tau_1 RLolly #c[$Q$] ⟧_(z_1) space bold("in") \
            &quad bold("let")_1 space z'_2 = (z_2, z') space bold("in") \
            &quad ⟦ #c[$Q_2 qtensor Q$] ; Gamma_2, x :_1 tau_1 ⊢ e_2 : tau ⟧_(z'_2) } \
          ⟦ #c[$Q$] ; Gamma ⊢ e : tau ⟧_(z) &=
          bold("let")_1 space z' = dsevidence(#c[$Q$] ⊩ #c[$Q_1$]) space z space bold("in") \
          &quad ⟦ #c[$Q_1$] ; Gamma ⊢ e : tau ⟧_(z') quad text("(-- rule E-Sub)")
        $
      ],
    )
  ]
]
#v(0.5em)

It is straightforward by induction, to verify that desugaring is correct:

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Theorem 7.1 (Desugaring).*
  If #c[$Q$] $; Gamma ⊢ e : tau$, then $dstype(Gamma), z :_1 dsevidence(#c[$Q$]) ⊢ ⟦ #c[$Q$] ; Gamma ⊢ e : tau ⟧_(z) : dstype(tau)$, for any fresh variable $z$.
]

Thanks to the desugaring machinery, the semantics of a language with linear constraints can be understood in terms of a simple core language with linear types, such as $lambda^q$, or indeed, GHC Core.
= Integrating into GHC
<sec:integrating-into-ghc>

One of the guiding principles behind our design was ease of integration with modern Haskell. In this section we describe some of the particulars of adding linear constraints to GHC.

== Implementation
<sec:implementation>

We have written a prototype implementation [Kiss et al. 2022] of linear constraints on top of GHC 9.1, a version that already ships with the `LinearTypes` extension. Function arrows (`->`) and context arrows (`=>`) share the same internal representation in the typechecker, differentiated only by a boolean flag. Thus, the `LinearTypes` implementation effort has already laid down the bureaucratic ground work of annotating these arrows with multiplicity information.

The key changes affect constraint generation and constraint solving. Constraints are now annotated with a multiplicity, according to the context from which they arise. With `LinearTypes`, GHC already scales the usage of term variables. We simply modified the scaling function to capture all the generated constraints and re-emit a scaled version of them, which is a fairly local change.

The constraint solver maintains a set of given constraints (the _inert set_ in GHC jargon), which corresponds to the #c[$U$], #c[$D$], and #c[$L$] contexts in our solver judgements in @sec:constraint-solver. When the solver goes under an implication, the assumptions of the implication are added to the set of givens. When a new given is added, we record the level of the implication (how many implications deep the constraint arises from) along with the constraint. So that in case there are multiple matching givens, the constraint solver selects the innermost one (in @sec:constraint-solver we use an ordered list for this purpose).

As constraint solving proceeds, the compiler pipeline constructs a term in a typed language known as GHC Core [Sulzmann et al. 2007]. In Core, type class constraints are turned into explicit evidence (see @sec:desugaring). Thanks to being fully annotated, Core has decidable typechecking, which is used to find and fix bugs in the compiler (the Haskell type checker finds mistakes in user programs). Thus, the Core typechecker verifies that the desugaring procedure produced a linearity-respecting program before code generation occurs.

== Interaction with Other Features
<sec:interaction-with-other-features>

Since constraints play an important role in GHC's type system, we must pay close attention to the interaction of linearity with other language features related to constraints. Of these, we point out two that require some extra care.

=== Superclasses
<sec:superclasses>

Haskell's type classes can have superclasses, which place constraints on all of the instances of that class. For example, the `Ord` class is defined as:

```haskell
class Eq a => Ord a where ...
```

which means that every ordered type must also support equality. Such superclass declarations extend the entailment relation: if we know that a type is ordered, we also know that it supports equality. This is troublesome if we have a linear occurrence of `Ord a`, because then using this entailment, we could conclude that a linear constraint (`Ord a`) implies an unrestricted constraint (`Eq a`), which violates Lemma 5.5.

But even linear superclass constraints cause trouble. Consider a version of `Ord a` that has `Eq a` as a linear superclass:

```haskell
class Eq a =⚬ Ord a where ...
```

When given a linear `Ord a`, should we keep it as `Ord a`, or rewrite to `Eq a` using the entailment? Short of backtracking, the constraint solver needs to make a guess, which GHC never does.

To address both of these issues at once, we make the following rule: _the superclasses of a linear constraint are ignored_.

=== Equality Constraints
<sec:equality-constraints>

In Section 6 we argued that type inference and constraint inference can be performed independently. However, this is not the case for GHC's constraint domain, because it supports equality constraints, which allows unification problems to be deferred, and potentially be solvable only after solving other constraints first.

To reconcile this with our presentation, we need to ensure that _unrestricted constraint inference_ and _linear constraint inference_ can be performed independently. That is, solving a linear constraint should never be required for solving an unrestricted constraint. This is ensured by Lemma 5.5.

The key is to represent unification problems as _unrestricted_ equality constraints, so a given linear equality constraint cannot be used during type inference. This way, linear equalities require no special treatment, and are harmless.

== Inferring Packing and Unpacking
<sec:implicit-existentials>

Recent work [Eisenberg, Duboc, et al. 2021] describes an algorithm (call it EDWL, after the authors' names) that can infer the location of the pack and unpack annotations (our $packbox$ and `let` $packbox$) in a program. In Section 9.2 of that paper, the authors extend their system to include class constraints, much as we allow our existential packages to carry linear constraints.

Accordingly, EDWL would work well for us here and remove the need for these annotations. The EDWL algorithm is only a small change on the way some types are treated during bidirectional type-checking. Though the presentation of linear constraints is not written using a bidirectional algorithm, our implementation in GHC is indeed bidirectional (as GHC's existing type inference algorithm is bidirectional, as described by Peyton Jones et al. [2007] and Eisenberg, Weirich, et al. [2016]) and produces constraints much like we have presented here, formally. None of this would change in adapting EDWL. Indeed, it would seem that the two extensions are orthogonal in implementation, though avoiding the need for explicit packing and unpacking would make linear constraints easier to use.
= Related Work
<sec:related-work>

*OutsideIn.* Our aim is to integrate the present work in GHC, and accordingly the qualified type system in Section 5 and the constraint inference algorithm in Section 6 follow a similar presentation to that of OutsideIn [Vytiniotis, Peyton Jones, Schrijvers, and Sulzmann 2011], GHC's constraint solver algorithm. Even though our presentation is self-contained, we outline some of the differences from that work.

The solver judgement in OutsideIn takes the following form:
$
  cal(Q) ; cal(Q)_("given") ; overline(alpha)_("tch") tack.rr^"solv" cal(C)_("wanted") leadsto cal(Q)_("residual") ; theta
$

The main differences from our solver judgement in @sec:constraint-solver are:
- OutsideIn's judgement includes top-level axioms schemes separately ($cal(Q)$), which we have omitted for the sake of brevity and are instead included in $cal(Q)_("given")$.
- We present the given constraints ($cal(Q)_("given")$ in OutsideIn) as two separate constraint sets #c[$U$] and #c[$L$], standing for the unrestricted and linear parts respectively.
- In addition to constraint inference, OutsideIn performs type inference, requiring additional bookkeeping in the solver judgment. The solver takes as input a set of touchable variables $overline(alpha)_("tch")$ which record the type variables that can be unified at any given time, and produces a type substitution $theta$ as an output. As discussed in Section 6, we do not perform type inference, only constraint inference. Therefore, our solver need not return a type assignment.
- Both OutsideIn and our solver output a set of constraints, $cal(Q)_("residual")$ and #c[$L_o$] respectively. However, the meaning of these contexts is different. OutsideIn's residual constraints $cal(Q)_("residual")$ correspond to the part of $cal(C)_("wanted")$ that could not be solved from the assumptions. These residuals are then quantified over in the generalisation step of the inference algorithm. We omit these residuals, which means that our algorithm cannot infer qualified types. Our output constraints #c[$L_o$] instead correspond to the part of the linear givens #c[$L_i$] that were not used in the solution for #c[$C_w$].
- Finally, while OutsideIn has a single kind of conjunction, our constraint language requires two: #c[$Q_1 qtensor Q_2$] and #c[$Q_1 aand Q_2$]. This shows up when generating constraints for case expressions in the rule `G_Case`. OutsideIn accumulates constraints across branches (taking the union of each branch), whereas we need to make sure that each branch of a case-expression consumes the same constraints.

*Ownership.* Ownership and borrowing are the key features of Rust's safe memory management model. In Section 4 we show how linear constraints can be used to implement such an ownership model as a library. Although linear constraints do not have the convenience of Rust's syntax, we expect that they will support a greater variety of abstractions.

Clean is another language with built-in ownership typing. Like Haskell it is a lazy language. Mutation is performed by returning a new reference, like in Linear Haskell without linear constraints.

*Languages with capabilities.* The idea of using capabilities to enforce high-level resource usage protocols is not new [DeLine and Fähndrich 2001], and as such has been applied in practical programming languages before. Both Mezzo [Pottier and Protzenko 2013] and ATS [Zhu and Xi 2005] served as inspiration for the design of linear constraints. Of the two, Mezzo is more specialised, being entirely built around its system of capabilities. ATS is the closest to our system because it appeals explicitly to linear logic, and because the capabilities (known as _stateful views_) are not tied to a particular use case. However, ATS does not have full inference of capabilities.

Other than that, the two systems have a lot of similarities. They have a finer-grained capability system than is expressible in Rust (or our encoding of it in Section 4) which makes it possible to change the type of a reference cell upon write (though linear constraints could be used to implement such type-changing references too). They also eschew scoped borrowing in favour of more traditional read and write capabilities.

Linear constraints are more general than either Mezzo or ATS, while maintaining a considerably simpler inference algorithm, and at the same time supporting a richer set of constraints (such as GADTs). This simplicity is a benefit of abstracting over the simple-constraint domain. In fact, it should be possible to see Mezzo or ATS as particular instantiations of the simple-constraint domain, with linear constraints providing the general inference mechanism.

*Linearly typed languages.* Affe [Radanne et al. 2020] is a linearly typed ML-style core language with mutable references and arrays, augmented with a notion of borrowing. It has dedicated syntax for the scope of borrows. In contrast, we represent scopes as functions. Affe is presented as a fully integrated solution, while linear constraints is a small layer on top of Linear Haskell.

*Logic programming.* There are a lot of commonalities between GHC's constraint and logic programs. Traditional type classes can be seen as Horn clause programs, much like Prolog programs. GHC puts further restrictions in order to avoid backtracking for speed and predictability.

The recent addition of quantified constraints [Bottu et al. 2017] extends type class resolution to Hereditary Harrop [Miller et al. 1987] programs. A generalisation of the Hereditary Harrop fragment to linear logic, described by Hodas and Miller [1994], is the foundation of the Lolli language [Hodas 1994]. The authors also coin the notion of _uniform proof_. A fragment where uniform proofs are complete supports goal-oriented proof search, like Prolog does.

Completeness of uniform proofs is equivalent to Lemma 6.1, which, in turn, is used in the proof of the soundness Lemma 6.4. Therefore our linear constraints are compatible with quantified constraints: we simply need to adapt Lemma 6.1.

It is interesting that goal-oriented search is baked into the definition of OutsideIn. It's not only used as the constraint solving strategy, but it seems to be required for the soundness of the constraint generation algorithm. Or, if they are not required, uniform proofs are at least an effective strategy to prove soundness.
= Conclusion
<sec:conclusion>

We showed how a simple linear type system like that of Linear Haskell can be extended with an inference mechanism which lets the compiler manage some of the additional complexity of linear types instead of the programmer. Linear constraints narrow the gap between linearly typed languages and dedicated linear-like typing disciplines such as Rust's, Mezzo's, or ATS's.
= Appendix: Full Descriptions
<sec:appendix:full-descriptions>

In this appendix, we give, for reference, complete descriptions of the type systems, functions, etc. that we have abbreviated in the main body of the article.

== Core calculus
<sec:appendix:core-calculus>

This is the complete version of the core calculus described in Section 7.1. The full grammar is given by Figure 13 and the type system by Figure 14.

#v(0.5em)
#align(center)[
  #block(
    fill: rgb("fafafa"),
    inset: 1em,
    stroke: 0.5pt + luma(200),
    radius: 3pt,
  )[
    #align(left)[
      *Figure 13: Grammar of the core calculus*
      #v(0.5em)
      $
        a, b &::= dots quad text("Type variables") \
        x, y &::= dots quad text("Expression variables") \
        K &::= dots quad text("Data constructors") \
        sigma &::= forall overline(a). tau quad text("Type schemes") \
        tau, upsilon &::= a mid(|) ∃ overline(a). tau_2 times.o tau_1 mid(|) tau_1 ->_pi tau_2 mid(|) T space overline(tau) quad text("Types") \
        Gamma, Delta &::= • mid(|) Gamma, x :_pi sigma quad text("Contexts") \
        e &::= x mid(|) K mid(|) lambda x. e mid(|) e_1 space e_2 mid(|) packbox space (e_1, e_2) quad text("Expressions") \
        &mid(|) bold("let") space packbox (y, x) = e_1 space bold("in") space e_2 mid(|) bold("case")_pi space e space bold("of") { overline(K_i space overline(x_i) -> e_i) } \
        &mid(|) bold("let")_pi space x = e_1 space bold("in") space e_2 mid(|) bold("let")_pi space x : sigma = e_1 space bold("in") space e_2
      $
    ]
  ]
]
#v(0.5em)

#block(
  fill: rgb("fafafa"),
  inset: 1em,
  stroke: 0.5pt + luma(200),
  radius: 3pt,
)[
  #align(center)[*Figure 14: Core calculus type system* ($Gamma ⊢ e : tau$)]

  #v(0.5em)
  #grid(
    columns: (1fr, 1fr),
    gutter: 1.5em,
    align: center + horizon,
    prooftree(rule(
      name: [L_Var],
      $x :_1 forall overline(a). upsilon in Gamma$,
      $Gamma ⊢ x : upsilon [overline(tau) / overline(a)]$,
    )),
    prooftree(rule(
      name: [L_Abs],
      $Gamma, x :_pi tau_1 ⊢ e : tau_2$,
      $Gamma ⊢ lambda x. e : tau_1 ->_pi tau_2$,
    )),
  )

  #v(0.8em)
  #prooftree(rule(
    name: [L_App],
    $Gamma_1 ⊢ e_1 : tau_1 ->_pi tau$,
    $Gamma_2 ⊢ e_2 : tau_1$,
    $Gamma_1 + pi cscale Gamma_2 ⊢ e_1 space e_2 : tau$,
  ))

  #v(0.8em)
  #prooftree(rule(
    name: [L_Pack],
    $Gamma_1 ⊢ e_1 : tau_1 [overline(upsilon) / overline(a)]$,
    $Gamma_2 ⊢ e_2 : tau_2 [overline(upsilon) / overline(a)]$,
    $Gamma_1 + Gamma_2 ⊢ packbox space (e_1, e_2) : ∃ overline(a). tau_2 times.o tau_1$,
  ))

  #v(0.8em)
  #prooftree(rule(
    name: [L_Unpack],
    $Gamma_1 ⊢ e_1 : ∃ overline(a). tau_2 times.o tau_1$,
    $overline(a) text(" fresh")$,
    $Gamma_2, x :_1 tau_1, y :_1 tau_2 ⊢ e_2 : tau$,
    $Gamma_1 + Gamma_2 ⊢ bold("let") space packbox (x, y) = e_1 space bold("in") space e_2 : tau$,
  ))

  #v(0.8em)
  #prooftree(rule(
    name: [L_Let],
    $Gamma_1 ⊢ e_1 : tau_1$,
    $Gamma_2, x :_pi sigma ⊢ e_2 : tau$,
    $pi cscale Gamma_1 + Gamma_2 ⊢ bold("let")_pi space x : sigma = e_1 space bold("in") space e_2 : tau$,
  ))

  #v(0.8em)
  #prooftree(rule(
    name: [L_Case],
    $Gamma_1 ⊢ e : T space overline(tau)$,
    $K_i : forall overline(a). overline(upsilon)_i ->_(overline(pi)_i) T space overline(a)$,
    $Gamma_2, overline(x_i :_((pi cscale pi_i)) upsilon_i [overline(tau) / overline(a)]) ⊢ e_i : tau$,
    $pi cscale Gamma_1 + Gamma_2 ⊢ bold("case")_pi space e space bold("of") { overline(K_i space overline(x_i) -> e_i) } : tau$,
  ))
]

== Desugaring
<sec:appendix:desugaring>

The complete definition of the desugaring function from Section 7 can be found in Figure 15.

For the sake of concision, we allow ourselves to write nested patterns in case expressions of the core language. Desugaring nested patterns into atomic case expression is routine.

In the complete description, we use a device which was omitted in the main body of the article. Namely, we'll need a way to turn every $dsevidence(#c[$omega cscale Q$])$ into an $mono("Ur") space (dsevidence(#c[$Q$]))$. For any $e : dsevidence(#c[$omega cscale Q$])$, we shall write $underline(e)_(#c[$Q$]) : mono("Ur") space (dsevidence(#c[$omega cscale Q$]))$. As a shorthand, particularly useful in nested patterns, we will write:
$
  bold("case")_pi space e space bold("of") { underline(x)_(#c[$Q$]) -> e' } quad text("for") quad bold("case")_pi space underline(e)_(#c[$Q$]) space bold("of") { mono("Ur") space x -> e' }
$

$
  cases(
    underline(e)_(ceps) = bold("case")_1 space e space bold("of") { () -> mono("Ur") space () },
    underline(e)_(#c[$1 cscale q$]) = e,
    underline(e)_(#c[$omega cscale q$]) = bold("case")_1 space e space bold("of") { mono("Ur") space x -> mono("Ur") space (mono("Ur") space x) },
    underline(e)_(#c[$Q_1 qtensor Q_2$]) = bold("case")_1 space e space bold("of") { (underline(x)_(#c[$Q_1$]), underline(y)_(#c[$Q_2$])) -> mono("Ur") space (x, y) },
  )
$

We will omit the #c[$Q$] in $underline(e)_(#c[$Q$])$ and write $underline(e)$ when it can be easily inferred from the context.

#v(0.5em)
#align(center)[
  #block(
    fill: rgb("fafafa"),
    inset: 1em,
    stroke: 0.5pt + luma(200),
    radius: 3pt,
  )[
    #align(center)[*Figure 15: Desugaring*]
    #v(0.5em)
    $
      ⟦ #c[$Q$] ; Gamma ⊢ x : upsilon [overline(tau) / overline(a)] ⟧_(z) &= x space z \
      ⟦ #c[$Q$] ; Gamma ⊢ lambda x. e : tau_1 ->_pi tau_2 ⟧_(z) &= lambda x. ⟦ #c[$Q$] ; Gamma, x :_pi tau_1 ⊢ e : tau_2 ⟧_(z) \
      ⟦ #c[$Q_1 qtensor Q_2$] ; Gamma_1 + Gamma_2 ⊢ e_1 space e_2 : tau ⟧_(z) &=
      bold("case")_1 space z space bold("of") { (z_1, z_2) -> \
        &quad (⟦ #c[$Q_1$] ; Gamma_1 ⊢ e_1 : tau_1 ->_1 tau ⟧_(z_1)) space (⟦ #c[$Q_2$] ; Gamma_2 ⊢ e_2 : tau_1 ⟧_(z_2)) } \
      ⟦ #c[$Q_1 qtensor omega cscale Q_2$] ; Gamma_1 + omega cscale Gamma_2 ⊢ e_1 space e_2 : tau ⟧_(z) &=
      bold("case")_1 space z space bold("of") { (z_1, underline(z_2)) -> \
        &quad (⟦ #c[$Q_1$] ; Gamma_1 ⊢ e_1 : tau_1 ->_omega tau ⟧_(z_1)) space (⟦ #c[$Q_2$] ; Gamma_2 ⊢ e_2 : tau_1 ⟧_(z_2)) } \
      ⟦ #c[$Q qtensor Q_1 [overline(upsilon) / overline(a)]$] ; Gamma ⊢ packbox space e : ∃ overline(a). tau RLolly #c[$Q_1$] ⟧_(z) &=
      bold("case")_1 space z space bold("of") { (z', z'') -> \
        &quad packbox space (z'', ⟦ #c[$Q$] ; Gamma ⊢ e : tau [overline(upsilon) / overline(a)] ⟧_(z')) } \
      ⟦ #c[$Q_1 qtensor Q_2$] ; Gamma_1 + Gamma_2 ⊢ bold("let") space packbox space x = e_1 space bold("in") space e_2 : tau ⟧_(z) &=
      bold("case")_1 space z space bold("of") { (z_1, z_2) -> \
        &quad bold("let") space packbox (z', x) = ⟦ #c[$Q_1$] ; Gamma_1 ⊢ e_1 : ∃ overline(a). tau_1 RLolly #c[$Q$] ⟧_(z_1) space bold("in") \
        &quad bold("let")_1 space z'_2 = (z_2, z') space bold("in") \
        &quad ⟦ #c[$Q_2 qtensor Q$] ; Gamma_2, x :_1 tau_1 ⊢ e_2 : tau ⟧_(z'_2) } \
      ⟦ #c[$Q_1 qtensor Q_2$] ; Gamma_1 + Gamma_2 ⊢ bold("let")_1 space x = e_1 space bold("in") space e_2 : tau ⟧_(z) &=
      bold("case")_1 space z space bold("of") { (z_1, z_2) -> \
        &quad bold("let")_1 space x : dsevidence(#c[$Q$]) ->_1 tau_1 = ⟦ #c[$Q_1 qtensor Q$] ; Gamma_1 ⊢ e_1 : tau_1 ⟧_(z_1) space bold("in") \
        &quad ⟦ #c[$Q_2$] ; Gamma_2, x :_1 tau_1 ⊢ e_2 : tau ⟧_(z_2) } \
      ⟦ #c[$omega cscale Q_1 qtensor Q_2$] ; omega cscale Gamma_1 + Gamma_2 ⊢ bold("let")_omega space x = e_1 space bold("in") space e_2 : tau ⟧_(z) &=
      bold("case")_1 space z space bold("of") { (underline(z_1), z_2) -> \
        &quad bold("let")_omega space x : dsevidence(#c[$Q$]) ->_1 tau_1 = ⟦ #c[$Q_1 qtensor Q$] ; Gamma_1 ⊢ e_1 : tau_1 ⟧_(z_1) space bold("in") \
        &quad ⟦ #c[$Q_2$] ; Gamma_2, x :_omega tau_1 ⊢ e_2 : tau ⟧_(z_2) } \
      ⟦ #c[$Q_1 qtensor Q_2$] ; Gamma_1 + Gamma_2 ⊢ bold("let")_1 space x : forall overline(a). #c[$Q$] Lolly tau_1 = e_1 space bold("in") space e_2 : tau ⟧_(z) &=
      bold("case")_1 space z space bold("of") { (z_1, z_2) -> \
        &quad bold("let")_1 space x : forall overline(a). dsevidence(#c[$Q$]) ->_1 tau_1 = ⟦ #c[$Q_1 qtensor Q$] ; Gamma_1 ⊢ e_1 : tau_1 ⟧_(z_1) space bold("in") \
        &quad ⟦ #c[$Q_2$] ; Gamma_2, x :_1 forall overline(a). #c[$Q$] Lolly tau_1 ⊢ e_2 : tau ⟧_(z_2) } \
      ⟦ #c[$omega cscale Q_1 qtensor Q_2$] ; omega cscale Gamma_1 + Gamma_2 ⊢ bold("let")_omega space x : forall overline(a). #c[$Q$] Lolly tau_1 = e_1 space bold("in") space e_2 : tau ⟧_(z) &=
      bold("case")_1 space z space bold("of") { (underline(z_1), z_2) -> \
        &quad bold("let")_omega space x : forall overline(a). dsevidence(#c[$Q$]) ->_1 tau_1 = ⟦ #c[$Q_1 qtensor Q$] ; Gamma_1 ⊢ e_1 : tau_1 ⟧_(z_1) space bold("in") \
        &quad ⟦ #c[$Q_2$] ; Gamma_2, x :_omega tau_1 ⊢ e_2 : tau ⟧_(z_2) } \
      ⟦ #c[$omega cscale Q_1 qtensor Q_2$] ; omega cscale Gamma_1 + Gamma_2 ⊢ bold("case")_1 space e space bold("of") { overline(K_i space overline(x_i) -> e_i) } : tau ⟧_(z) &=
      bold("case")_1 space z space bold("of") { (underline(z_1), z_2) -> \
        &quad bold("case")_1 space (⟦ #c[$Q_1$] ; Gamma_1 ⊢ e : T space overline(tau) ⟧_(z_1)) space bold("of") { \
          &quad quad overline(K space overline(x)_i -> ⟦ #c[$Q_2$] ; Gamma_2, overline(x_i :_((pi cscale pi_i)) upsilon_i [overline(tau) / overline(a)]) ⊢ e_i : tau ⟧_(z_2)) } } \
      ⟦ #c[$Q_1 qtensor Q_2$] ; Gamma_1 + Gamma_2 ⊢ bold("case")_omega space e space bold("of") { overline(K_i space overline(x_i) -> e_i) } : tau ⟧_(z) &=
      bold("case")_1 space z space bold("of") { (z_1, z_2) -> \
        &quad bold("case")_omega space (⟦ #c[$Q_1$] ; Gamma_1 ⊢ e : T space overline(tau) ⟧_(z_1)) space bold("of") { \
          &quad quad overline(K space overline(x)_i -> ⟦ #c[$Q_2$] ; Gamma_2, overline(x_i :_((pi cscale pi_i)) upsilon_i [overline(tau) / overline(a)]) ⊢ e_i : tau ⟧_(z_2)) } }
    $
  ]
]
= Appendix: Proofs
<sec:appendix:proofs-lemmas>

== Lemmas on the qualified type system
<sec:appendix:lemmas-qualified-system>

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Proof of Lemma 5.4.* Let us prove separately the cases $pi = 1$ and $pi = omega$.
  - When $pi = 1$, then $pi cscale Q = Q$ for all $Q$, hence #c[$Q_1$] $⊩$ #c[$Q_2$] implies #c[$pi cscale Q_1$] $⊩$ #c[$pi cscale Q_2$].
  - For the case $pi = omega$, let us consider a few properties. First note that, for any $Q$, #c[$omega cscale Q = omega cscale Q qtensor omega cscale Q$]. From which it follows, using the laws of Definition 5.3, that #c[$omega cscale Q$] $⊩$ #c[$Q_1 qtensor Q_2$] if and only if #c[$omega cscale Q$] $⊩$ #c[$Q_1$] and #c[$omega cscale Q$] $⊩$ #c[$Q_2$].\
    This means that to verify that #c[$omega cscale Q_1$] $⊩$ #c[$omega cscale Q_2$], it is equivalent to prove that #c[$omega cscale Q_1$] $⊩$ #c[$omega cscale q_2$] for each $q_2 in U$ (letting #c[$omega cscale Q_2 = (U, emptyset)$]). In turn, by Definition 5.3 and observing that #c[$omega cscale (omega cscale Q_1) = Q_1$], this is equivalent to #c[$omega cscale Q_1$] $⊩$ #c[$1 cscale q_2$].\
    This follows from the fact that #c[$Q_1$] $⊩$ #c[$Q_2$] implies #c[$omega cscale Q_1$] $⊩$ #c[$Q_2$] (Definition 5.3) and the property, shown above, that #c[$omega cscale Q_1$] $⊩$ #c[$Q_2 qtensor Q'_2$] if and only if #c[$omega cscale Q_1$] $⊩$ #c[$Q_2$] and #c[$omega cscale Q_1$] $⊩$ #c[$Q'_2$]. $qed$
]

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Proof of Lemma 5.5.* Let us prove separately the cases $pi = 1$ and $pi = omega$.
  - When $pi = 1$, then $pi cscale Q = Q$ for all $Q$, in particular #c[$Q_1$] $⊩$ #c[$1 cscale Q_2$] implies that #c[$Q_1 = 1 cscale Q_1$] with #c[$Q_1$] $⊩$ #c[$Q_2$].
  - When $pi = omega$, then let us first remark, letting #c[$omega cscale Q_2 = (U, emptyset)$] that, by a straightforward induction on the cardinality of $U$ it is sufficient to prove that the result holds for atomic constraints.\
    That is, we need to prove that if #c[$Q_1$] $⊩$ #c[$omega cscale q_2$] then there exists #c[$Q'$] such that #c[$Q_1 = omega cscale Q'$] and #c[$Q'$] $⊩$ #c[$rho cscale q_2$] (for all $rho$).\
    This result, in turn, holds by Definition 5.3. $qed$
]

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Lemma B.1.* The following equality holds: #c[$pi cscale (rho cscale Q) = (pi cscale rho) cscale Q$].\
  *Proof.* Immediate by case analysis of $pi$ and $rho$. $qed$
]

== Lemmas on constraint inference
<sec:appendix:lemmas-constraint-inference>

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Lemma B.2 (#c[$cal(D)$] discarding).* The two following, equivalent, properties hold:
  - If #c[$Q_cal(D) in cal(D)$], then #c[$Q_cal(D)$] $⊩ ceps$
  - If #c[$Q_1$] $⊩$ #c[$Q_2$] and #c[$Q_cal(D) in cal(D)$], then #c[$Q_1 qtensor Q_cal(D)$] $⊩$ #c[$Q_2$]

  *Proof.* The two properties are equivalent:
  - Using #c[$Q_1 = Q_2 = ceps$], the latter implies the former.
  - The former implies the latter by tensoring together #c[$Q_1$] $⊩$ #c[$Q_2$] and #c[$Q_cal(D)$] $⊩ ceps$ following the rules of Figure 4.

  Let #c[$Q_cal(D) in cal(D)$], then for each #c[$1 cscale q in Q_cal(D)$], #c[$1 cscale q$] $⊩ ceps$ (per Figure 4), tensoring each of these entailments together and with the #c[$omega cscale q in Q_cal(D)$], we get #c[$Q_cal(D)$] $⊩ ceps$. $qed$
]

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Lemma B.3 (#c[$cal(D)$] duplication).* The two following, equivalent, properties hold:
  - If #c[$Q_cal(D) in cal(D)$], then #c[$Q_cal(D)$] $⊩$ #c[$Q_cal(D) qtensor Q_cal(D)$]
  - If #c[$Q_1 qtensor Q_cal(D)$] $⊩$ #c[$Q_2$], #c[$Q_cal(D) qtensor Q'_1$] $⊩$ #c[$Q'_2$], and #c[$Q_cal(D) in cal(D)$], then #c[$Q_1 qtensor Q_cal(D) qtensor Q'_1$] $⊩$ #c[$Q_2 qtensor Q'_2$]

  *Proof.* The proof is similar to that of Lemma B.2. $qed$
]

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Lemma B.4 (Transitive tensor decomposition).* If #c[$Q_cal(D) in cal(D)$] and #c[$Q$] $⊩$ #c[$Q_1 qtensor Q_cal(D) qtensor Q_2$], then there exist #c[$Q'_1$], #c[$Q'_cal(D)$], #c[$Q'_2$], such that:
  - #c[$Q'_1 qtensor Q'_cal(D)$] $⊩$ #c[$Q_1$]
  - #c[$Q'_cal(D) qtensor Q'_2$] $⊩$ #c[$Q_2$]
  - #c[$Q'_cal(D)$] $⊩$ #c[$Q_cal(D)$]

  *Proof.* By the inversion-of-tensor rule from Figure 4, we get that there exist #c[$Q'$], #c[$Q'_cal(D)$], and #c[$Q'_2$], such that:
  - #c[$Q = Q' qtensor Q'_cal(D) qtensor Q'_2$]
  - #c[$Q'_cal(D) qtensor Q'_2$] $⊩$ #c[$Q_2$]
  - #c[$Q' qtensor Q'_cal(D)$] $⊩$ #c[$Q_1 qtensor Q_cal(D)$]. The inversion-of-tensor rule applies further to this case: there exist #c[$Q'_1$], #c[$Q''_cal(D)$], and #c[$Q''$] such that:
    - #c[$Q' qtensor Q'_cal(D) = Q'_1 qtensor Q''_cal(D) qtensor Q''$]
    - #c[$Q'_1 qtensor Q''_cal(D)$] $⊩$ #c[$Q_1$]
    - #c[$Q''_cal(D) qtensor Q''$] $⊩$ #c[$Q_cal(D)$]

  Observe the following:
  - #c[$Q''_cal(D) qtensor Q'' in cal(D)$] (because of the requirements of Figure 4). Let's write #c[$Q'''_cal(D) = Q''_cal(D) qtensor Q''$].
  - #c[$Q = Q'_1 qtensor Q'''_cal(D) qtensor Q'_2$]
  - We have:
    - #c[$Q'_1 qtensor Q'''_cal(D)$] $⊩$ #c[$Q_1$]. Because #c[$Q'_1 qtensor Q'''_cal(D) = Q' qtensor Q'_cal(D)$], therefore #c[$Q'_1 qtensor Q'''_cal(D)$] $⊩$ #c[$Q_1 qtensor Q_cal(D)$]. By Lemma B.2, and by transitivity of the entailment relation (per Figure 4), we can drop #c[$Q_cal(D)$] from the conclusion.
    - #c[$Q'''_cal(D)$] $⊩$ #c[$Q_cal(D)$] (by definition of #c[$Q'''_cal(D)$]).
    - #c[$Q'''_cal(D) qtensor Q'_2$] $⊩$ #c[$Q_2$]: By tensoring together, per Figure 4, #c[$Q'''_cal(D)$] $⊩$ #c[$Q'_cal(D)$] and #c[$Q'_2$] $⊩$ #c[$Q'_2$], we get #c[$Q'''_cal(D) qtensor Q'_2$] $⊩$ #c[$Q'_cal(D) qtensor Q'_2$], then we get the desired result by transitivity of the entailment relation.

  This concludes the proof. $qed$
]

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Proof of Lemma 6.1.* The cases #c[$Q ⊢ C_1 aand C_2$] and #c[$Q ⊢ pi cscale (Q_2 Lolly C)$] are straightforward by induction, so let us prove them first:
  - Suppose #c[$Q ⊢ C_1 aand C_2$], then there are two cases:
    - Either it is the conclusion of a `C_With` rule, and the result is immediate.
    - Or it is the result of a `C_Dom` rule, then, there exists #c[$Q'$], such that #c[$Q ⊩ Q'$] and #c[$Q' ⊢ C_1 aand C_2$]. By induction #c[$Q' ⊢ C_1$] and #c[$Q' ⊢ C_2$], applying `C_Dom` to both gives #c[$Q ⊢ C_1$] and #c[$Q ⊢ C_2$] as required.
  - Suppose #c[$Q ⊢ pi cscale (Q_2 Lolly C)$], then there are two cases:
    - Either it is the conclusion of a `C_Impl` rule, and the result is immediate.
    - Or it is the result of a `C_Dom` rule, then, there exists #c[$Q'$], such that #c[$Q ⊩ Q'$] and #c[$Q' ⊢ pi cscale (Q_2 Lolly C)$]. By induction, there exists #c[$Q'_1$] such that #c[$Q'_1 qtensor Q_2 ⊢ C$] and #c[$Q' = pi cscale Q'_1$], by Figure 4, there exists #c[$Q_1$] such that #c[$Q = pi cscale Q_1$] and #c[$Q_1 ⊩ Q'_1$]. Hence #c[$Q_1 qtensor Q_2 ⊩ Q'_1 qtensor Q_2$], which lets us conclude with `C_Dom`.

  For #c[$Q ⊢ C_1 qtensor C_2$] we have the following cases:
  - Either it is the conclusion of a `C_Tensor` rule, and the result is immediate.
  - Or it is the result of a `C_Id` rule, in which case #c[$Q = C_1 qtensor C_2$], which proves the result.
  - Or it is the result of a `C_Dom` rule, in which case there is #c[$Q'$] such that #c[$Q ⊩ Q'$] and #c[$Q' ⊢ C_1 qtensor C_2$]. By induction, there exist #c[$Q'_1$], #c[$Q'_cal(D)$], and #c[$Q'_2$], such that #c[$Q'_cal(D) in cal(D)$], #c[$Q'_1 qtensor Q'_cal(D) ⊢ C_1$], #c[$Q'_cal(D) qtensor Q'_2 ⊢ C_2$], and #c[$Q' = Q'_1 qtensor Q'_cal(D) qtensor Q'_2$].\
    Then Lemma B.4 gives us #c[$Q_1$], #c[$Q_cal(D)$], and #c[$Q_2$] such that:
    - #c[$Q = Q_1 qtensor Q_cal(D) qtensor Q_2$]
    - #c[$Q_cal(D) in cal(D)$]
    - #c[$Q_1 qtensor Q_cal(D) ⊩ Q'_1$]
    - #c[$Q_cal(D) qtensor Q_2 ⊩ Q'_2$]
    - #c[$Q_cal(D) ⊩ Q'_cal(D)$]\
    By Lemma B.3, we can further deduce that:
    - #c[$Q_1 qtensor Q_cal(D) ⊩ Q'_1 qtensor Q'_cal(D)$]
    - #c[$Q_cal(D) qtensor Q_2 ⊩ Q'_cal(D) qtensor Q'_2$]\
    Which concludes the proof, by the `C_Dom` rule. $qed$
]

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Proof of Lemma 6.2.* By induction on the syntax of #c[$C$]:
  - If #c[$C = Q'$], then the result follows from Lemma 5.4.
  - If #c[$C = C_1 qtensor C_2$], then we can prove the result like we proved the corresponding case in Lemma 5.4, using Lemma 6.1.
  - If #c[$C = C_1 aand C_2$], then the case where $pi = 1$ is immediate, so we can assume without loss of generality that $pi = omega$, and, therefore, that #c[$pi cscale C = pi cscale C_1 qtensor pi cscale C_2$]. By Lemma 6.1, we have that #c[$Q ⊢ C_1$] and #c[$Q ⊢ C_2$]; hence, by induction, #c[$pi cscale Q ⊢ pi cscale C_1$] and #c[$pi cscale Q ⊢ pi cscale C_2$]. Then, by definition of the entailment relation, we have #c[$omega cscale Q qtensor omega cscale Q ⊢ omega cscale C_1 qtensor omega cscale C_2$], which concludes, since #c[$omega cscale Q = omega cscale Q qtensor omega cscale Q$].
  - If #c[$C = rho cscale (Q_1 Lolly C')$], then by Lemma 6.1, there is a #c[$Q'$] such that #c[$Q = rho cscale Q'$] and #c[$Q' qtensor Q_1 ⊢ C'$]. Applying rule `C_Impl` with $pi cscale rho$, we get #c[$(pi cscale rho) cscale Q' ⊢ (pi cscale rho) cscale (Q_1 Lolly C')$]. In other words: #c[$pi cscale Q ⊢ pi cscale (rho cscale (Q_1 Lolly C'))$] as expected. $qed$
]

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Proof of Lemma 6.3.* By induction on the syntax of #c[$C$]:
  - If #c[$C = Q'$], then the result follows from Lemma 5.5.
  - If #c[$C = C_1 qtensor C_2$], then we can prove the result like we proved the corresponding case in Lemma 5.5 using Lemma 6.1.
  - If #c[$C = C_1 aand C_2$], then the case where $pi = 1$ is immediate, so we can assume without loss of generality that $pi = omega$, and, therefore, that #c[$pi cscale C = pi cscale C_1 qtensor pi cscale C_2$]. By Lemma 6.1, there exist #c[$Q_1$] and #c[$Q_2$] such that #c[$Q_1 ⊢ pi cscale C_1$], #c[$Q_2 ⊢ pi cscale C_2$] and #c[$Q = Q_1 qtensor Q_2$]. By induction hypothesis, we get #c[$Q_1 = omega cscale Q'_1$] and #c[$Q_2 = omega cscale Q'_2$] such that #c[$Q'_1 ⊢ C_1$] and #c[$Q'_2 ⊢ C_2$]. From which it follows that #c[$omega cscale Q'_1 qtensor omega cscale Q'_2 ⊢ C_1$] and #c[$omega cscale Q'_1 qtensor omega cscale Q'_2 ⊢ C_2$] (by Lemma B.5) and, finally, #c[$Q = omega cscale Q$] (by Lemma B.6) and #c[$Q ⊢ C_1 aand C_2$].
  - If #c[$C = rho cscale (Q_1 Lolly C')$], then #c[$pi cscale C = (pi cscale rho) cscale (Q_1 Lolly C')$]. The result follows immediately by Lemma 6.1. $qed$
]

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Proof of Lemma 6.4.* By induction on $Gamma vdashi e : tau leadsto$ #c[$C$]:

  - *G_Var:* We have:
    - $Gamma_1 = x :_1 forall overline(a). #c[$Q$] Lolly upsilon$
    - $Gamma_1 + omega cscale Gamma_2 vdashi x : upsilon [overline(tau) / overline(a)] leadsto #c[$Q [overline(tau) / overline(a)]$]$
    - #c[$Q_g$] $⊢$ #c[$Q [overline(tau) / overline(a)]$]
    Therefore, by rules `E_Var` and `E_Sub`, it follows immediately that #c[$Q_g$] $; Gamma_1 + omega cscale Gamma_2 ⊢ x : upsilon [overline(tau) / overline(a)]$.

  - *G_Abs:* We have:
    - $Gamma vdashi lambda x. e : tau_0 ->_pi tau leadsto$ #c[$C$]
    - #c[$Q_g$] $⊢$ #c[$C$]
    - $Gamma, x :_pi tau_0 vdashi e : tau leadsto$ #c[$C$]
    By induction hypothesis we have #c[$Q_g$] $; Gamma, x :_pi tau_0 ⊢ e : tau$, from which follows that #c[$Q_g$] $; Gamma ⊢ lambda x. e : tau_0 ->_pi tau$.

  - *G_Let:* We have:
    - $pi cscale Gamma_1 + Gamma_2 vdashi bold("let")_pi space x = e_1 space bold("in") space e_2 : tau leadsto #c[$pi cscale C_1 qtensor C_2$]$
    - #c[$Q_g$] $⊢$ #c[$pi cscale C_1 qtensor C_2$]
    - $Gamma_2, x :_pi tau_1 vdashi e_2 : tau leadsto$ #c[$C_2$]
    - $Gamma_1 vdashi e_1 : tau_1 leadsto$ #c[$C_1$]
    By Lemmas 6.1 and 6.3, there exist #c[$Q_1$], #c[$Q_cal(D)$] and #c[$Q_2$] such that:
    - #c[$Q_1 qtensor Q_cal(D)$] $⊢$ #c[$C_1$]
    - #c[$Q_cal(D) qtensor Q_2$] $⊢$ #c[$C_2$]
    - #c[$Q_g = pi cscale Q_1 qtensor Q_cal(D) qtensor Q_2$]
    - #c[$Q_cal(D) in cal(D)$]
    - #c[$pi cscale Q_cal(D) = Q_cal(D)$]
    By induction hypothesis we have:
    - #c[$Q_1 qtensor Q_cal(D)$] $; Gamma_1 ⊢ e_1 : tau_1$
    - #c[$Q_cal(D) qtensor Q_2$] $; Gamma_2, x :_pi tau_1 ⊢ e_2 : tau$
    From which follows that #c[$Q_g$] $; pi cscale Gamma_1 + Gamma_2 ⊢ bold("let")_pi space x = e_1 space bold("in") space e_2 : tau$.

  - *G_LetSig:* We have:
    - $pi cscale Gamma_1 + Gamma_2 vdashi bold("let")_pi space x : forall overline(a). #c[$Q$] Lolly tau_1 = e_1 space bold("in") space e_2 : tau leadsto #c[$C_2 qtensor pi cscale (Q Lolly C_1)$]$
    - #c[$Q_g$] $⊢$ #c[$C_2 qtensor pi cscale (Q Lolly C_1)$]
    - $Gamma_1 vdashi e_1 : tau_1 leadsto$ #c[$C_1$] with $overline(a)$ fresh
    - $Gamma_2, x :_pi forall overline(a). #c[$Q$] Lolly tau_1 vdashi e_2 : tau leadsto$ #c[$C_2$]
    By Lemmas 6.1 and 6.3, there exist #c[$Q_1$], #c[$Q_cal(D)$], #c[$Q_2$] such that:
    - #c[$Q_cal(D) qtensor Q_2$] $⊢$ #c[$C_2$]
    - #c[$Q_1 qtensor Q_cal(D) qtensor Q$] $⊢$ #c[$C_1$]
    - #c[$Q_g = pi cscale Q_1 qtensor Q_cal(D) qtensor Q_2$]
    - #c[$Q_cal(D) in cal(D)$]
    - #c[$pi cscale Q_cal(D) = Q_cal(D)$]
    By induction hypothesis:
    - #c[$Q_1 qtensor Q_cal(D) qtensor Q$] $; Gamma_1 ⊢ e_1 : tau_1$
    - #c[$Q_cal(D) qtensor Q_2$] $; Gamma_2, x :_pi forall overline(a). #c[$Q$] Lolly tau_1 ⊢ e_2 : tau$
    Hence #c[$Q_g$] $; pi cscale Gamma_1 + Gamma_2 ⊢ bold("let")_pi space x : forall overline(a). #c[$Q$] Lolly tau_1 = e_1 space bold("in") space e_2 : tau$.

  - *G_App:* We have:
    - $Gamma_1 + pi cscale Gamma_2 vdashi e_1 space e_2 : tau leadsto #c[$C_1 qtensor pi cscale C_2$]$
    - #c[$Q_g$] $⊢$ #c[$C_1 qtensor pi cscale C_2$]
    - $Gamma_1 vdashi e_1 : tau_2 ->_pi tau leadsto$ #c[$C_1$]
    - $Gamma_2 vdashi e_2 : tau_2 leadsto$ #c[$C_2$]
    By Lemmas 6.1 and 6.3, there exist #c[$Q_1$], #c[$Q_cal(D)$], #c[$Q_2$] such that:
    - #c[$Q_1 qtensor Q_cal(D)$] $⊢$ #c[$C_1$]
    - #c[$Q_cal(D) qtensor Q_2$] $⊢$ #c[$C_2$]
    - #c[$Q_g = Q_1 qtensor Q_cal(D) qtensor pi cscale Q_2$]
    - #c[$Q_cal(D) in cal(D)$]
    - #c[$pi cscale Q_cal(D) = Q_cal(D)$]
    By induction hypothesis:
    - #c[$Q_1 qtensor Q_cal(D)$] $; Gamma_1 ⊢ e_1 : tau_2 ->_pi tau$
    - #c[$Q_cal(D) qtensor Q_2$] $; Gamma_2 ⊢ e_2 : tau_2$
    Hence #c[$Q_g$] $; Gamma_1 + pi cscale Gamma_2 ⊢ e_1 space e_2 : tau$.

  - *G_Pack:* We have:
    - $Gamma vdashi packbox space e : ∃ overline(a). tau RLolly #c[$Q$] leadsto #c[$C qtensor Q [overline(upsilon) / overline(a)]$]$
    - #c[$Q_g$] $⊢$ #c[$C qtensor Q [overline(upsilon) / overline(a)]$]
    - $Gamma vdashi e : tau [overline(upsilon) / overline(a)] leadsto$ #c[$C$]
    By Lemma 6.1, there exist #c[$Q_1$], #c[$Q_cal(D)$], #c[$Q_2$] such that:
    - #c[$Q_1 qtensor Q_cal(D)$] $⊢$ #c[$C$]
    - #c[$Q_cal(D) qtensor Q_2$] $⊢$ #c[$Q [overline(upsilon) / overline(a)]$]
    - #c[$Q_g = Q_1 qtensor Q_cal(D) qtensor Q_2$]
    - #c[$Q_cal(D) in cal(D)$]
    By induction hypothesis:
    - #c[$Q_1 qtensor Q_cal(D)$] $; Gamma ⊢ e : tau [overline(upsilon) / overline(a)]$
    So we have #c[$Q_1 qtensor Q_cal(D) qtensor Q [overline(upsilon) / overline(a)]$] $; Gamma ⊢ packbox space e : ∃ overline(a). tau RLolly #c[$Q$]$. By Lemma B.3 and rule `E_Sub`, we conclude #c[$Q_g$] $; Gamma ⊢ packbox space e : ∃ overline(a). tau RLolly #c[$Q$]$.

  - *G_Unpack:* We have:
    - $Gamma_1 + Gamma_2 vdashi bold("let") space packbox space x = e_1 space bold("in") space e_2 : tau leadsto #c[$C_1 qtensor 1 cscale (Q' Lolly C_2)$]$
    - #c[$Q_g$] $⊢$ #c[$C_1 qtensor 1 cscale (Q' Lolly C_2)$]
    - $Gamma_1 vdashi e_1 : ∃ overline(a). tau_1 RLolly #c[$Q'$] leadsto$ #c[$C_1$]
    - $Gamma_2, x :_1 tau_1 vdashi e_2 : tau leadsto$ #c[$C_2$]
    By Lemma 6.1, there exist #c[$Q_1$], #c[$Q_cal(D)$], #c[$Q_2$] such that:
    - #c[$Q_1 qtensor Q_cal(D)$] $⊢$ #c[$C_1$]
    - #c[$Q_cal(D) qtensor Q_2 qtensor Q'$] $⊢$ #c[$C_2$]
    - #c[$Q_g = Q_1 qtensor Q_cal(D) qtensor Q_2$]
    - #c[$Q_cal(D) in cal(D)$]
    By induction hypothesis:
    - #c[$Q_1 qtensor Q_cal(D)$] $; Gamma_1 ⊢ e_1 : ∃ overline(a). tau_1 RLolly #c[$Q'$]$
    - #c[$Q_cal(D) qtensor Q_2 qtensor Q'$] $; Gamma_2, x :_1 tau_1 ⊢ e_2 : tau$
    Therefore #c[$Q_g$] $; Gamma_1 + Gamma_2 ⊢ bold("let") space packbox space x = e_1 space bold("in") space e_2 : tau$.

  - *G_Case:* We have:
    - $pi cscale Gamma + Delta vdashi bold("case")_pi space e space bold("of") { overline(K_i space overline(x_i) -> e_i) } : tau leadsto #c[$pi cscale C qtensor bigaand C_i$]$
    - #c[$Q_g$] $⊢$ #c[$pi cscale C qtensor bigaand C_i$]
    - $Gamma vdashi e : T space overline(sigma) leadsto$ #c[$C$]
    - For each $i$, $Delta, overline(x_i :_((pi cscale pi_i)) upsilon_i [overline(sigma) / overline(a)]) vdashi e_i : tau leadsto #c[$C_i$]$
    By repeated uses of Lemma 6.1 as well as Lemma 6.3, there exist #c[$Q$], #c[$Q_cal(D)$], #c[$Q'$] such that:
    - #c[$Q qtensor Q_cal(D)$] $⊢$ #c[$C$]
    - For each $i$, #c[$Q_cal(D) qtensor Q'$] $⊢$ #c[$C_i$]
    - #c[$Q_g = pi cscale Q qtensor Q_cal(D) qtensor Q'$]
    - #c[$Q_cal(D) in cal(D)$]
    - #c[$pi cscale Q_cal(D) = Q_cal(D)$]
    By induction hypothesis:
    - #c[$Q qtensor Q_cal(D)$] $; Gamma ⊢ e : T space overline(sigma)$
    - For each $i$, #c[$Q_cal(D) qtensor Q'$] $; Delta, overline(x_i :_((pi cscale pi_i)) upsilon_i [overline(sigma) / overline(a)]) ⊢ e_i : tau$
    Therefore #c[$Q_g$] $; pi cscale Gamma + Delta ⊢ bold("case")_pi space e space bold("of") { overline(K_i space overline(x_i) -> e_i) } : tau$. $qed$
]

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Proof of Lemma 6.5.* By induction on #c[$U$] $;$ #c[$D$] $;$ #c[$L_i$] $vdashs$ #c[$C$] $leadsto$ #c[$L_o$]:

  - *S_Atom:* We have:
    - #c[$U$] $;$ #c[$D$] $;$ #c[$L_i$] $vdashs$ #c[$pi cscale q$] $leadsto$ #c[$L_o$]
    - #c[$U$] $;$ #c[$D$] $;$ #c[$L_i$] $vdashsimp$ #c[$pi cscale q$] $leadsto$ #c[$L_o$]
    By Property 6.6 we have:
    1. #c[$L_o$] $subset.eq$ #c[$L_i$]
    2. #c[$(U, D uplus L_i)$] $⊩$ #c[$pi cscale q qtensor (emptyset, L_o)$]
    Then by `C_Dom` we have #c[$(U, D uplus L_i)$] $⊢$ #c[$pi cscale q qtensor (emptyset, L_o)$].

  - *S_Add:* We have:
    - #c[$U$] $;$ #c[$D$] $;$ #c[$L_i$] $vdashs$ #c[$C_1 aand C_2$] $leadsto$ #c[$L_o$]
    - #c[$U$] $;$ #c[$D$] $;$ #c[$L_i$] $vdashs$ #c[$C_1$] $leadsto$ #c[$L_o$]
    - #c[$U$] $;$ #c[$D$] $;$ #c[$L_i$] $vdashs$ #c[$C_2$] $leadsto$ #c[$L_o$]
    By induction hypothesis we have:
    - #c[$L_o$] $subset.eq$ #c[$L_i$]
    - #c[$(U, D uplus L_i)$] $⊢$ #c[$C_1 qtensor (emptyset, L_o)$]
    - #c[$(U, D uplus L_i)$] $⊢$ #c[$C_2 qtensor (emptyset, L_o)$]
    Then by `C_With` we have #c[$(U, D uplus L_i)$] $⊢$ #c[$(C_1 aand C_2) qtensor (emptyset, L_o)$].

  - *S_Mult:* We have:
    - #c[$U$] $;$ #c[$D$] $;$ #c[$L_i$] $vdashs$ #c[$C_1 qtensor C_2$] $leadsto$ #c[$L_o$]
    - #c[$U$] $;$ #c[$D$] $;$ #c[$L_i$] $vdashs$ #c[$C_1$] $leadsto$ #c[$L'_o$]
    - #c[$U$] $;$ #c[$D$] $;$ #c[$L'_o$] $vdashs$ #c[$C_2$] $leadsto$ #c[$L_o$]
    By induction hypothesis we have:
    - #c[$L_o$] $subset.eq$ #c[$L'_o$]
    - #c[$L'_o$] $subset.eq$ #c[$L_i$]
    - #c[$(U, D uplus L_i)$] $⊢$ #c[$C_1 qtensor (emptyset, L'_o)$]
    - #c[$(U, D uplus L'_o)$] $⊢$ #c[$C_2 qtensor (emptyset, L_o)$]
    Then:
    - By transitivity of $subset.eq$ we have #c[$L_o$] $subset.eq$ #c[$L_i$], and by `C_Tensor` we have #c[$(U, D uplus L_i) qtensor (U, D uplus L'_o)$] $⊢$ #c[$C_1 qtensor C_2 qtensor (emptyset, L'_o) qtensor (emptyset, L_o)$].
    - By Lemma B.3 and the definition of tensor on unrestricted constraints, we have #c[$(U, D uplus L_i) qtensor (emptyset, L'_o)$] $⊢$ #c[$C_1 qtensor C_2 qtensor (emptyset, L'_o) qtensor (emptyset, L_o)$].
    - By Lemma 6.1 we have #c[$(U, D uplus L_i)$] $⊢$ #c[$C_1 qtensor C_2 qtensor (emptyset, L_o)$].

  - *S_ImplOne:* We have:
    - #c[$U$] $;$ #c[$D$] $;$ #c[$L_i$] $vdashs$ #c[$1 cscale ((U_0, L_0) Lolly C)$] $leadsto$ #c[$L_o$]
    - #c[$U union U_0$] $;$ #c[$D uplus (L_0 inter cal(D))$] $;$ #c[$L_i uplus (L_0 backslash cal(D))$] $vdashs$ #c[$C$] $leadsto$ #c[$L_o$]
    - #c[$L_o$] $subset.eq$ #c[$L_i$]
    By induction hypothesis we have:
    - #c[$(U union U_0, D uplus L_i uplus L_0)$] $⊢$ #c[$C qtensor (emptyset, L_o)$]
    - #c[$L_o$] $subset.eq$ #c[$L_i uplus L_0$]
    Then we know that #c[$(emptyset, L_i) = (emptyset, L_o) qtensor (emptyset, L'_i)$] for some $L'_i$. Then by Lemma 6.1 we know that #c[$(U union U_0, D uplus L'_i uplus L_0)$] $⊢$ #c[$C$] and by `C_Impl` we have #c[$(U, D uplus L'_i)$] $⊢$ #c[$1 cscale ((U_0, L_0) Lolly C)$]. Finally, by `C_Tensor` we conclude that #c[$(U, D uplus L_i)$] $⊢$ #c[$1 cscale ((U_0, L_0) Lolly C) qtensor (emptyset, L_o)$].

  - *S_ImplMany:* We have:
    - #c[$U$] $;$ #c[$D$] $;$ #c[$L_i$] $vdashs$ #c[$omega cscale ((U_0, L_0) Lolly C)$] $leadsto$ #c[$L_i$]
    - #c[$U union U_0$] $;$ #c[$L_0 inter cal(D)$] $;$ #c[$L_0 backslash cal(D)$] $vdashs$ #c[$C$] $leadsto$ #c[$emptyset$]
    By induction hypothesis we have:
    - #c[$(U union U_0, L_0)$] $⊢$ #c[$C$]
    Then by `C_Impl` #c[$(U, emptyset)$] $⊢$ #c[$omega cscale ((U_0, L_0) Lolly C)$] and finally by rule `C_Tensor` we have #c[$(U, D uplus L_i)$] $⊢$ #c[$omega cscale ((U_0, L_0) Lolly C) qtensor (emptyset, L_i)$]. #c[$L_i$] $subset.eq$ #c[$L_i$] holds trivially. $qed$
]

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Lemma B.5 (Weakening of wanteds).* If #c[$Q$] $⊢$ #c[$C$], then #c[$omega cscale Q' qtensor Q$] $⊢$ #c[$C$].\
  *Proof.* This is proved by a straightforward induction on the derivation of #c[$Q$] $⊢$ #c[$C$], using the corresponding property on the simple-constraint entailment relation from Definition 5.3, for the `C_Dom` case. $qed$
]

#block(stroke: 0.5pt + luma(180), inset: 0.8em, radius: 3pt)[
  *Lemma B.6.* The following equality holds: #c[$pi cscale (rho cscale C) = (pi cscale rho) cscale C$].\
  *Proof.* This is proved by a straightforward induction on the structure of #c[$C$], using Lemma B.1 for the case #c[$C = Q$]. $qed$
]
