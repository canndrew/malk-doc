# Let's make a language

This document is a brain-dump of ideas for a programming language. I'm putting
it out here in the hope that there are other people with vaguely similar aims
and ideas who might want to collaborate on building something.

Because it's hard to talk about something without a name, I'm refering to this
hypothetical language as "malk".

## Aims of this language

The essentials:
  * Full dependent types. The ability to freely mix types and values, have
    types depend on runtime values and use this to implement provably-correct
    code much like in Idris or Agda.
  * Close to the metal. I want to be able to reason about the runtime
    behaviour of my code and have a vague sense of what the corresponding
    machine code looks like. This implies having pointer types and explicit
    heap usage as well as linear/affine types for writing efficient code (much
    like in, eg, Rust). It also implies being able to interface with C code,

Things that I'd like but could compromise on:
  * Extreme simplicity. The fewer underlying concepts and syntax classes the better.
    Ideally I'd like: no global scope, everything is an expression, modules are
    just structs, structs are just tuples. etc. Something like a
    statically-typed Lua.
  * Is it's own metaprogramming language. Related to the above point, Terra is
    a programming language where your program is a Lua script which runs at
    compile time and generates a blob of LLVM IR which gets turned into an
    executable. Since dependently typed languages have to be able to run
    arbitrary code at compile time anyway, and since they have the ability to
    generate new types at runtime, you could do a similar thing with a
    dependently typed language except where both the language and the
    meta-language are the same. An example of something you could do with this
    is instead of having an import/use keyword, just have an import function
    which load a module at compile time.
  * Useful for embedding. Again, since dependently typed languages need to have
    a scripty side to them (they need to be able to run in the compiler's
    interpretter and on the target machine) and since they allow you to prove
    correctness of the compiled code, they would be perfect for use in
    untrusted environments.
  * Whitespace irrelevance. Explicitness over conciseness (within reason). No
    overloading, invisible casts, user-defined operators or any horrible shit
    like that.

### And so

The reason I'm writing is that every six months for the last ten years I've
decided to make a programming language, worked manically on it for a month,
realised the enormous amount of work ahead of me, then given up. Maybe I'm
lazy, but maybe there's others out there that have had the same experience and
who share a similar vision. And maybe we could all benefit from sharing the
workload.

To the above ends, what follows is a rough outline of what such a programming
language might look like. **This is just a starting point.** If you're reading
this and you like some of the ideas but not the implementation then lets talk
and start changing things until we get something we'd both want to build. There
are still gaping holes in this very rough design and I change my ideas all the
time anyway.


# Basic types and syntax

Note: The main point of defining the syntax in such detail is so that the rest
of this document makes sense, not because I'm particulary commited to this
syntax.

## Numeric types

Malk has numeric types.

    Integers:

    Type                    Type syntax     example value syntax
    unsigned 8bit           U8              123u8
    unsigned 16bit          U16             123u16
    unsigned 32bit          U32             123u32
    unsigned 64bit          U64             123u64
    signed 8bit             I8              123i8
    signed 16bit            I16             123i16
    signed 32bit            I32             123i32
    signed 64bit            I64             123i64
    unsigned memory-sized   Um              123um
    signed memory-sized     Im              123im
    unsigned big ints       Ubig            123ubig
    signed big ints         Ibig            123ibig

These are mostly the same as Rust's numeric types except that the type names
start with an uppercase letter (eg. U32 instead of u32). This follows the
convention of type names being in UpperCamelCase although it does look kinda
ugly. Malk also has big ints as primitive types because these are very useful
for proving things without having to take into account the posibility of
overflow.

There are also floating point types: `F32`, `F64`, which use plain old Rust/C
value syntax.

## The unit type

There is a unit type, aka. `void` (in C), aka. `()` (in Rust, Haskell, etc.).
It has two syntactic forms:

The type itself is written `#{}`. the unit value is written `{}`. Because we're
working with dependent types it's important for these two forms to have
different syntax. In something like rust or haskell you can distinguish between
the type `()` and the value `()` based on context, but with dependent types the
type is also a value and can appear in the same positions as any other value.
It's a convention in this doc to make type syntax resemble the corresponding
value syntax except captilised or prefixed with a `#`.

There is also a pattern match form (used for writing function which take a
`#{}` argument) which is also written `{}`.

## Pair types

There is a (dependent) pair type. The type form is written `#{head_name:
HeadType, .. TailType}` and the value form is written `{head_name = head_value,
.. tail_value}`. The tail type can be dependent on the head type. There's also
a pattern-match form written `{head_name = head_pattern, .. tail_pattern}`
which can be used to extract the head and the tail and bind them to variables.
The head can also be indexed by writing `my_pair.head_name`.

Naming the head is optional, so `{head_value, .. tail_value} : #{HeadType, ..
TailType}` is also valid syntax. If the head name is omitted in a value then
the syntax is ambiguous: `{head_value, .. tail_value}` may have type
`#{HeadType, ..  TailType}` but may also have type `#{some_name: HeadType, ..
TailType}`

Pairs a represented as two contiguous elements in memory, in a compiler-defined
ordering, possibly seperated by padding.

## Structs

Pair types would not usually be used directly in practice. Their main purpose is to
serve as a primitive for inductively building/consuming struct types. Structs contain
any number of elements and their syntax looks like this:

    type:    #{name_a: TypeA, name_b: TypeB, name_c: TypeC}
    value:    {name_a = value_a, name_b = value_b, name_c = value_c}
    pattern:  {name_a = patten_a, name_b = patten_b, name_c = patten_c}

Struct types are just syntactic sugar for tail-nested pairs terminated with a
unit. ie. The above type could also be written
    
    #{name_a: TypeA, .. #{name_b: TypeB, .. #{name_c: TypeC, .. #{}}}}

We can specify any number of head elements before collecting the rest of the
struct into the tail. So this is also valid syntax for the same type:

    #{name_a: TypeA, name_b: TypeB, .. #{name_c: TypeC}}

Malk's structs serve as a replacement for the tuple and (ordered) struct types
found in other languages. By using dependent functions (introduced later) they
can also serve as a replacement for array types.

Indexing a pair recurses into the tail element if the name of the head element
doesn't match. This way we can write `{x = 0, y = 1, z = 2}.y` to get the value
`2`.

Multiple fields of a struct can also have the same name. This is necessary
because structs are built inductively from pairs and so there is no sane way to
avoid it. This is unlikely to matter much in practice as people will not
deliberately duplicate field names. It may occur when people are
programatically generating struct types in such a way that they can't control
the field names, but in this case they'll have to be using pattern-matching -
not indexing - to destructure values of these types.

The tail element of a pair does not need to be a struct, this is a perfectly
valid type: `#{U32, .. U32}`. However the only way to create types and values
like this is to work directly with pairs rather than at the usual level of
structs.

Since structs are composed of pairs, the compiler is not free to arbitrarily
reorder struct elements. For a struct of n elements it has 2^(n - 1) different
orderings to choose from. This is still better than C (where structs are
ordered) but not as good as (say) Rust where the compiler can reorder in n!
different ways.

## Functions

Malk has dependent function types. Function types are written *pattern* `->`
*return type*. Function values are written *pattern* `=>` *return value*. The
pattern specifies the argument type of the function as well as how to
destructure and name-bind the argument. The simplest pattern simply gives a
name to bind the argument to: `x => x` is the identity function on an
unspecified type. Patterns can also be parenthesised or be given type
annotations: `(x: U32) -> U32` is the type of functions which take a `U32`
(named `x`) and return a `U32`.

Struct and pair arguments can be destructured in the pattern position and names
bound to their elements:

    // function which takes a unit and returns 23u32
    {} => 23u32

    // function which takes a `#{x: U32, y: U32}` and sums the elements.
    {x = bind_x: U32, y = bind_y: U32} => bind_x + bind_y

    // another function which takes a `#{x: U32, y: U32}` and sums the
    // elements. If the names of the argument struct elements are not
    // explicitly specified then they are assumed to be the names that the
    // elements are bound to (here `x` and `y`).
    {x: U32, y: U32} => x + y

    // functions which take a pair `#{x: U32, .. U32}` and sum the elements
    {x = bind_x: U32, .. y: U32} => bind_x + y
    {x: U32, .. y: U32} => x + y

For unsigned ints, we consider them to be inductively defined by a zero and a
successor constructor and allow pattern matching on them by handling the two
cases seperately.

    // A function that takes n and returns (n - 1) (or 0 when n = 0).
    [
        0     => 0u32,
        1 + n => n,
    ];

In malk, function applictation is written without parenthesis (eg. `func arg`)
like in many functional programming languages. However many functions will take
a struct as their argument allowing us to write things like `func {123, 456}`.
Note that this also gives us named arguments for free. Function application can
also be written backwards using the `in` keyword: `arg in func`.

All functions are unboxed closures. They are represented as a function pointer
followed by the closure data. Importantly, this means that two functions of the
same type might not have the same size. In general, size is a property of
values, not types, although for many types all values will have the same size.
All types are represented such that size can also be calculated at runtime by
inspecting the value. Usually though this information will already be available
at compile time (even in the case of functions). For function types, the length
of the closure data can be stored immediately before the start of the machine
code. This means it can always be retrieved using the function pointer. If we
need to ensure that a function has no closure data (eg.  when exposing an API
to C) then we can just check that the size of the function is equal to the size
of a pointer.

## Never type

There is a never type (aka. `Void`, `Empty`, `⊥`, `!`). The type is written
`#[]`. This type has no values. A function out of this type can be written simply
as `[]`. For example, if we have `x: #[]`, then `[] x` or `x in []` is an empty
match that creates a value of an infered type.

## Sum types

There are sum types, ie. disjoint unions of two types. The type form is written
`#[left_name: LeftType, .. RightType]`. This has two different value
constructors written `[left_name = left_value]` and `[.. right_value]`.
Functions out of these types are written much like functions out of integers:

    [
        left_name = left_pattern    => expr,
        .. right_pattern            => expr,
    ]

## Enums

Like pair types, sum types are not meant to be used directly in most
circumstances. Instead we have enum types which are just syntactic sugar for
nested sums terminated in never. Enum syntax looks like this:

    type:       #[name_a: TypeA, name_b: TypeB, name_c: TypeC]
    values:      [name_x = value_x]
    function:    [
                    name_a = pattern_a => expr,
                    name_b = pattern_b => expr,
                    name_c = pattern_c => expr,
                 ]

The above type is syntax sugar for the type:

    #[name_a: TypeA, .. #[name_b: TypeB, .. #[name_c: TypeC, .. #[]]]]

And the above function is syntax sugar for:

    [
        name_a = pattern_a => expr,
        .. right           => right in [
            name_b = pattern_b  => expr,
            .. right            => right in [
                name_c = pattern_c  => expr,
                .. right            => right in [],
            ]
        ]
    ]

`[name_b = value_b]` is ambiguous but is inferred to mean:

    `[.. [name_b = value_b]]`

## The `Type` type.

There is a type of all types, called `Type`. Technically speaking, for logical
consistency, there is an infinite, cumulative hierarchy of types called `Type
?0`, `Type ?1`, `Type ?2` etc. indexed by an int-like supertype called `Level`,
but all these details are usually hidden by inference. I'll talk more about
inference and implicit arguments later.

Because `Type` is a type, we can write functions that return types or take
types as arguments. This is how we can write polymorphic functions.

# `let` expressions

`let` expressions can be used to bind values to a variable. The syntax is `let
pattern = value; expr`. Example:

    // These three lines are one big expression which evaluates to 3
    let x: U32 = 1;
    let y: U32 = 2;
    x + y

Type annotations can be omitted where the type can be inferred. Variables can
also be shadowed by later let expressions.

    // Also evaluates to 3
    let x = 1;
    let x = x + 2;
    x

In malk, everything is defined by being assigned to a variable like this, even
top-level types and functions.

# Implicit and erased variables

_Note: I'm not sure that actually makes sense to identify erased and inferred
variables like I do here. I'm just trying to cut down on syntax._

## Erasure

Some values have no runtime relevance and only need to exist for typechecking.
We would like these values to be erased. meaning we don't end up carrying them
around at runtime. Malk provides a way to mark a variable as erased by
prefixing the name with `?`.

Example:

    // Suppose we have a type which is generic over U32,
    let Foo: (x: U32) -> Type = #{};

    // We can create an erased value called x...
    let ?x: U32 = 23;

    // And use it in a type
    let y: Foo x = {};

Erased values cannot be used in any non-erased expression, only to the right of
a `:` or in other erased expressions. This means that this code will not compile:

    // Create an erased value called x...
    let ?x: U32 = 23;

    // ERROR! Trying to assign x to a runtime value.
    let z: U32 = x;

Erased variables can be created anywhere where normal variables can be created,
not just in let expressions. eg. we can write functions that take an erased
argument: `(?x: U32) -> Foo x`, or put them in structs/enums: `#{?x: U32}`.

## Implicit arguments

Erased variables are predominantly used in the types of other variables. As
such, their value can often be inferred from the types of these other values.
For example, suppose we have this function:

    f: {?n: U32, v: Foo n} -> U32

When we pass in the value of `v` (which has some known type such as `Foo 23`),
we can infer the value of `n` (such as `23`). In these cases, we do not need to
give the values of erased arguments explicitly - we can call `f` by writing `f
{my_foo}`. If we do want to specify the value of the erased/implicit
argument we have to prefix it with `?`: `f {?23, my_foo}`.

Similarly, if a function takes an implicit arg directly (not within a struct)
we need to do the same thing: `my_func ?23`.

The motivation for allowing these arguments to be implicit is that, when
writing generic code, there tends to be *lots* of these arguments and it can be
a lot work to plumb them through explicitly.

## At the type level

Technically, there are two kinds of function types, two kinds of pair type and
two kinds of sum type. There's the non-erased, explicit versions and the
erased, implicit versions. Syntax such as `{foo = 23}` is actually ambiguous
and could typecheck as something like `#{?implicit0: T0, ?implicit1: T1,
?implicit2: T2, foo: U32}`

# More types

Let's get to some slightly more advanced types.

## Equality types

Malk has equality types. These are types that represent a proof that
two expressions are equal.

### Examples

This is a type:

    2 + 2 #= 4

It represents all proofs that two plus two is four. There is only one such
proof, it is the value `2 + 2 == 4` (or equivalently `4 == 4` since `2 + 2`
normalises to `4`). This value contains no data, the type as a whole is
isomorphic to `#{}`.

This is also a type:

    2 + 2 #= 5

It represents all proofs that two plus two is five. Of which there are none.
This type is empty, meaning it has no values and is isomorphic to `#[]`.

### Usage

One place you might want this is in writing a division function which requires
proof that the divisor is non-zero.

    safe_divide: {
        numerator: U32,
        divisor: U32,
        ?divisor_is_non_zero: (divisor #= 0) -> #[],
    } -> U32

If we allow `divisor_is_non_zero` to be infered (see the section on inference)
then we can call this function like this:

    safe_divide {10, 2}

But if we try to call it with zero, then the inference for
`divisor_is_non_zero` will fail.

    safe_divide {10, 0}    // compile error

If `divisor` is not a literal then we'll need to manually construct a value for
`divisor_is_non_zero` or pass one in from somewhere. For example:

    divide_twice = {
        numerator: U32,
        divisor: U32,
        ?divisor_is_non_zero: (divisor #= 0) -> #[],
    } => (
        let once = safe_divide {numerator, divisor, ?divisor_is_non_zero};
        let twice = safe_divide {once, divisor, ?divisor_is_non_zero};
        twice
    )

### Elimination

Equalities can be pattern-matched on. A function which takes an equality arg
can be written like:

    (a == b) => ...

Here, `a` and `b` must be the names of variables, not arbitrary expressions.
The effect of this pattern matching is that, in the function body, `a` and `b`
are treated as equal. In particular, when ever the compiler checks for the
definitional equality of two expressions it does so under a context. This
context contains all the information about the variables that are in scope and
the patterns that created them. Implementation-wise, the `a == b` pattern
creates a hidden variable that both `a` and `b` normalise to - but only during
equality checking. What this means is that it can typecheck and validate
a function like this:

    let symmetry = {
        ?Ty: Type,
        ?a: Ty,
        ?b: Ty,
        a == b,
    } => b == a;

Which is given the type:

    {?Ty: Type, ?a: Ty, ?b: Ty, a #= b} -> b #= a

We can also prove transitivity of equality similarly.

    let transitivity = {
        ?Ty: Type,
        ?a: Ty,
        ?b: Ty,
        ?c: Ty,
        a == b,
        b == c,
    } => a == c;

This typechecks because:

 0. `a == b` makes `a` and `b` both reduce to some imaginary variable `x`.
 1. `b == c` reduces to `x == c` and makes `x` and `c` both reduce to some
    imaginary variable `y`.
 2. `a == c` reduces to `y == y`, equality passes, and the body expression is
    given type `a #= c`.

Type-theory-wise, I'm pretty sure this corresponds to the J axiom, but doesn't
allow you to prove K. I would need to formalise all this to be completely sure.
Not having K is important if we want to one day extend this language with
something like cubical type theory.

### More usage

Here's a couple of other useful functions we can write for manipulating proofs:

    // Shows that any function preserves equality
    let congruence = {
        ?A: Type,
        ?B: A -> Type,
        ?x: A,
        ?y: A,
        func: (a: A) -> B a,
        x == y
    } => func x == func y;

    // Given two types, and a proof that they're equal, create a map from one
    // type to the other.
    let transport = {
        ?A: Type,
        ?B: Type,
        A == B
    } => (x: A) => (x: B)

Using these functions, we can prove that non-zero numbers are non-zero. The
aforementioned inference for `divisor_is_non_zero` could look like this:

    let impl (n: U32): (1 + n #= 0) -> #[]
                     = (p: 1 + n #= 0) => (
        let int_to_type = [
            0       => #[],
            1 + n   => #{},
        ];
        let unit_is_never = congruence {int_to_type, p};
        let unit_to_never = transport {unit_is_never};
        unit_to_never {}
    )

### Types are better than `Bool`.

One thing to notice here is that `1 + 1 == 2` has type `1 + 1 #= 2` - not
`Bool`. In fact, there is no equality operator that returns `Bool` because when
you have dependent types you can do much better. So what do we do if we want to
test the equality of two things? We use the `Decision` type:

    let Decision = (Ty: Type) => #[
        proof: Ty,
        disproof: Ty -> #[],
    ];

`Decision Ty` represents a proof or disproof of `Ty`, ie. either an inhabitant
of `Ty` or a proof that `Ty` is uninhabited. We can then create these decisions
for any decidable type using the `decide` function.

    let decide = (Ty: Type) => ?(d: Decision Ty) => d;

This relies on inference to get a decision for `Ty` and returns it.

Suppose we want to make a wrapper for our `safe_divide` function that doesn't
demand a proof of `divisisor_is_non_zero` but returns an error on zero instead:

    let try_divide = {
        numerator: U32,
        divisor: U32,
    } -> Result {U32, DivideByZeroError}
      => (
        decide (divisor #= 0) in [
            proof    => [error = divide_by_zero_error],
            disproof => [ok = safe_divide {numerator, divisor, disproof}].
        ]
    )

This is an example of the advantage of `Decision` over `Bool`. Rather than
telling you that "something" was true/false, it tells you what was true/false
and carries the corresponding proof. That proof has to be used in a typesafe
way (you can't use a proof of `A` as a proof of `B`) and it can be used for
typechecking (in this case by passing it to `safe_divide`).

### Cubical types?

Cubical type theory, an implementation of HoTT, provides a much richer form of
equality types where proofs of equality can carry information and where more
things are possible or easier to prove. For example, with cubical types, you
can prove that two functions are equal when they have the same I/O behaviour
(ie `f #= g` when `f x #= g x` for all `x`) and that two types are equal when
they're isomorphic.

This is cool and useful but might clash with the idea of this being a language
for low-level programming. Fuzzing over things like the in-memory
representation of types and the computational complexity of functions makes,
for example, quicksort equal to shuffle sort. I don't know how much of a
problem this would be in practice, but I'd want to ensure that the compiler
doesn't swap out one algorithm for a less efficient one or reorder my structs
when I care about their representation. 

## Recursive types

Recursion in dependently typed languages can be tricky to do right. You can't
just allow any function to call any other function with any argument at any
time or else the language will be inconsistent as a logic and none of the
proofs in it will be valid. A trivial example of this is that you could write a
function that returns `#[]` by just calling itself in a loop:
`let f = {} -> #[] => (foo {})` and then you can create a term `foo {}: #[]`.
Seen as a logic, this corresponds to allowing proofs that contain circular
logic to prove a negative (ie. `#[]` is true because `#[]` is true).

To fix this we have to guarantee that all recursion is *well-founded*. This
means that if a function somehow ends up calling itself, it can only do so if
the sub-invocation is given an argument that is "smaller" than the argument
given to the original invocation. Here, the meaning of "smaller" can depend on
the type of the argument in question, we just need to guarantee that if you
take any argument (eg. `n: U32`) and keep making it smaller and smaller (eg. `n
=> n - 1`) you eventually won't be able to make it any smaller (eg. because `n
== 0`) and therefore recursion has to stop.

Languages like Idris and Agda achieve this through an analysis pass which
analyses the call-graph of all the functions in your code looking for cycles.
If it finds one (eg. `f` calls `g` calls `h` calls `f`) then it makes sure that
the argument given to the sub-invocation is smaller than the original. This
approach has a couple of problems though. Firstly, it's not clearly visible in
the code whether a function is valid or not because you need to consider all
the functions that it may call indirectly. Secondly, it uses a very strict
definition of "smaller than" which isn't reflected in the language and doesn't
allow the programmer to construct their own proofs that a recursive call is
valid.

Malk solves this through the addition of two new kinds of type, recursive types
and subterm types, which we'll explore below.

Although restricting recursion in the way described below makes the language
non-turing-complete, this isn't as bad as it might sound. Obstensibly, it just
means it's not possible to write a program that goes into an infinite loop
without ever producing output, but we also have the option of adding
turing-completeness back in through an intrinsic or effect only available at
runtime,

### `Rec` types

In malk we can only use a variable once it's been assigned a value:

    let x = y;  // ERROR! y is undefined
    let y = 2;

We can also shadow previous variables by rebinding the name:

    let x = 1;
    let x = x + 1;
    x == 2

Given this, how could we even *try* to define a recursive type?

Enter:`Rec`. `Rec` allows you to write expressions of type `Type` which are
recursive.

    Rec Nat #[zero: #{}, pred: Nat]

The above expression represents the type of unary natural numbers. The first
argument to `Rec` is a name which will refer to the name of the type we are
defining. The second argument is a type expression which may refer to the given
name (in this case `Nat`). The expression given above refers to an infinite
type which looks like:

    #[zero: #{}, pred: #[zero: #{}, pred: #[zero: #{}, pred: ... ]]]

If we want to assign this type to a variable called `Nat` we can do so in two
ways: either the long way or using the shorthand `let Rec` syntax sugar:

    let Nat: Type = Rec Nat #[zero: #{}, pred: Nat];
    // alternatively
    let Rec Nat = #[zero: #{}, pred: Nat];

Once we've defined our type we can create terms and match on them normally like this:

    let zero: Nat = [zero = {}];
    let one: Nat = [pred = [zero = {}]];

    let is_zero: Nat -> Bool
               = [
        zero => [true = {}],
        pred => [false = {}],
    ];

However if we want to write a recursive function out of `Nat` we have to do
things a little differently.

    let is_even: Nat -> Bool
            = (rec n ~ is_even_n) => n in [
        zero => [true = {}],
        pred => not (is_even_n pred),
    ];

This wierd bit of syntax - `(rec n ~ is_even_n)` - binds two names for use in
the function body: `is_even_n` is the name of the function we're defining and
`n` is the name of the function argument. However there's a twist: instead of
`Nat -> Bool` and `Nat`, `is_even_n` and `n` have types `~n -> Bool` and
`#[zero: #{}, pred: ~n]`. So what's `~n`?

### Subterm types `~expr`

For any expression `expr` there is a type of subterms of that expression
`~expr` representing all terms with the same type as `expr` that are
*structurally smaller* than `expr`. Here, the meaning of "structurally smaller"
depends on the type of `expr`:
  * For unsigned ints, "structurally smaller" means "less than".
  * For strings it means "substring of".
  * For `[head = super]` it means terms `[head = sub]` where `sub` is
    structurally smaller than `super`.
  * For `[; super]` it means either `[head = anything]` or `[; sub]` where sub
    is structurally smaller than `super`.
  * For `{super_a, super_b}` it means `{sub_a, sub_b}` where `sub_a` is
    structurally smaller than `super_a` OR `sub_a` equals `super_a` and `sub_b`
    is structurally smaller than `super_b`.
  * For recursive types, it means the subterm is equal to or structurally
    smaller than one of the occurances of the type within itself in the super
    term. eg. for `Nat`, `foo` is smaller than `[pred = foo]` and `[pred =
    [pred = foo]]` etc.
  * For every other type, no term is structurally smaller than any other.

It should be clear that the above rules define a well-founded partial order on
every type.

Now that we have some definitions, let's look at that `even` function up close
and see that it typechecks.

    let is_even: Nat -> Bool
            = (rec n ~ is_even_n) => (

        // Here we have:
        //    is_even_n: ~n -> Bool
        //    n: #[zero: #{}, pred: ~n]

        n in [
            zero => [true = {}],
            pred => (
                
                // Here we have
                //    is_even_n: ~n -> Bool
                //    pred: ~n
            
                not (is_even_n pred)
            ),
        ]
    );

Here's an extended example showing how to write mutually recursive types and
functions.

    // Being defined first, Bar takes Foo as an argument.
    let Bar = (Foo: Type) => #[
        val: U32,
        foo: Foo,
    ];

    // Foo recursively passes itself to Bar. This means that when we do a
    // recursive pattern-match on `ff: Foo`, we will have `bar: Bar ~ff`,
    let Rec Foo = #[
        val: U32,
        bar: Bar Foo,
    ];

    // Being defined first, get_bar takes both Foo and get_foo as arguments.
    let get_bar = {
        ?Foo: Type,
        get_foo: Foo -> U32,
        bb: Bar Foo,
    } => bb in [
        val => val,
        foo => get_foo {foo},
    ];

    let get_foo = {(rec ff ~ get_foo): Foo} => ff in [
        val => val,
        bar => get_bar {get_foo, bar},

        // Or, with everything written out explicitly:
        bar => get_bar {
            ?Foo: Type = ~ff
            get_foo: ~ff -> Bar = get_foo,
            bb: Bar ~ff = bar,
        },
    ];

    // Alternatively, we could define get_bar inside the body of get_foo for
    // more conciseness.

    let get_foo = {(rec ff ~ get_foo): Foo} => (
        let get_bar = {bb: Bar ~ff} => bb in [
            val => val,
            foo => get_foo {foo},
        ];
        ff in [
            val => val,
            bar => get_bar {get_foo, bar},
        ]
    );

    // There's also a `let rec` shorthand for writing recursive functions. For
    // `get_foo` this would look like:

    let rec get_foo = (ff: Foo) => (
        let get_bar = (bb: Bar ~ff) => bb in [
            val => val,
            foo => get_foo foo,
        ];
        ff in [
            val => val,
            bar => get_bar get_foo bar,
        ]
    )

### Subtyping on subterm types.

For any `expr: E`, `~expr` is a subtype of `E`. This allows us to prove
theorems about subterms which may be useful in situations where we have more
complicated recursion. For example, earlier we said.

> For `{super_a, super_b}` it means `{sub_a, sub_b}` where [..] `sub_a` equals
> `super_a` and `sub_b` is structurally smaller than `super_b`.

We can prove this as such:

    let wow = {a, sub_b}: #{A, ~super_b}
           => {a, sub_b}: ~{a, super_b}

When typechecking this function, the typechecking algorithm will
  * Check whether `a` has type `~a`
  * It doesn't (because `a` has type `A`). So instead check whether `a` is
    judgementally equal to `a`.
  * It is, so check whether `sub_b` has type `~super_b`.
  * It does, so `{a, sub_b}` can have type `~{a, super_b}`.

This rather limited form of subtyping does not carry with it some of the
problems found with richer forms of subtyping. There is no need to translate
between the different types. For example, with `expr: E`  a pointer to type
`~expr` is also a pointer to type `E` even at the lowest level of the language
implementation.







# TODO:

  * pointers
  * effects
  * controlling inference
  * impls
  * static vs dynamic dispatch
      after types, traits
  * linear types
  * strings and idents

