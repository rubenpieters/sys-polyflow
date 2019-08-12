# Search Terms

generic indexed access type dependent function

# Suggestion

TypeScript does not provide dependent types, but by combining various features such as unions, literal types and indexed access types we can obtain fairly similar behaviour to a dependent function from the caller point of view. Unfortunately, the implementer of such functions is faced with either the possibility of creating unsoundness (pre 3.5) or forced to assert the return type with unsound features (post 3.5). There are some differences with typical dependent functions, which is why we call these _dependent-type-like_ functions.

This suggestion proposes an addition to the typechecking part of TypeScript, which aids the programmer in writing dependent-type-like functions. The main attractive point of this suggestion is that it does not introduce any additional syntax, and is meant to be a conservative extension. Thus it is not a breaking change with regards to the changes introduced in 3.5, but it does enable certain sound scenarios to typecheck.

# Use Case

The main use case are dependent-type-like functions, the `depLikeFun` example is a minimalistic scenario showcasing such a situation. In this example, we have the `depLikeFun` function which returns `number` when its input is of type `"t"` and `boolean` when its input is of type `"f"`.

```ts
interface F {
  "t": number,
  "f": boolean,
}

function depLikeFun<T extends "t" | "f">(str: T): F[T] {
  if (str === "t") {
    return 1;
  } else {
    return true;
  }
}

depFun("t"); // has type number
depFun("f"); // has type boolean
```

This pattern occurs in various places, such as the [TypeScript dom bindings](https://github.com/microsoft/TypeScript/blob/ca00b3248b1af2263d0223d68e792b7ca39abcab/lib/lib.dom.d.ts#L11050), in issues such as [#31672](https://github.com/microsoft/TypeScript/issues/31672) and [#32698](https://github.com/microsoft/TypeScript/issues/32698), in comments of related issues such as [#13995](https://github.com/microsoft/TypeScript/issues/13995), or on [stackoverflow questions](https://stackoverflow.com/questions/56479117/how-to-fix-ts2322-when-using-a-case-switch-and-generics). This extension could serve as a workaround for related issues such as [#22609](https://github.com/microsoft/TypeScript/issues/22609) and [#23861](https://github.com/microsoft/TypeScript/issues/23861).

TODO: does this help with [#25879](https://github.com/microsoft/TypeScript/issues/25879) ?
TODO: does this pattern occur somewhere in [fp-ts](https://github.com/gcanti/fp-ts) ?

# Problem

The problem lies in the implementation of the function. The pre-3.5 behaviour enabled the creation of unsoundness in these type of functions. TypeScript checked the return value against the union of its possibilities, which is `number | boolean`. However, this is unsound since the caller expects different behaviour based on the function signature.

```ts
// pre-3.5
function depLikeFun<T extends "t" | "f">(str: T): F[T] {
  if (str === "t") {
    return true; // should be error
  } else {
    return 1; // should be error
  }
}

depLikeFun("t"); // has type number, but is actually a boolean
depLikeFun("f"); // has type boolean, but is actually a number
```

The post-3.5 behaviour also isn't satisfactory for this use case. It disallows the `depLikeFun` to be implemented, which means the implementer needs to use unsafe type assertions. By [#30769](https://github.com/microsoft/TypeScript/issues/30739), the `return` calls are considered writes to the result of the function. This means that the result type `F[T]` is checked against the _intersection_ of its possibilities, which is `number & boolean` and thus `never`. 

```ts
// post-3.5
function depLikeFun<T extends "t" | "f">(str: T): F[T] {
  if (str === "t") {
    return 1; // unexpected error: '1' is not assignable to never
  } else {
    return true; // unexpected error: 'true' is not assignable to never
  }
}
```

Mistakes are more likely to occur in complex situations, and thus aiding the user with these types of functions seems in line with TypeScript's design goals.

# Examples

In a dependently typed language `depLikeFun` would be modeled as `function depFun(str: "t" | "f"): F[str]`. There are meaningful differences between depending on the actual _value_ of the input versus the _type_ of an input. This distinction makes this issue more tricky to solve than appears on first sight. In this section we showcase the expected behaviour of the addition on certain representative examples.

The main idea behind the addition is as follows. in a dependent-type-like function we cannot narrow the type `T` of a variable when the value of that value is checked. For example, if `str` has type `T extends "t" | "f"` and we check whether `str === "t"`, then it is unsafe to narrow `T` to `"t"` in that branch, since `T` could also be instantiated with for example `"t" | "f"`. Instead, we add knowledge about the type `T` within the branch which is more conservative, but makes it possible to allow the behaviour of dependent-type-like functions. In more traditional programming language theory, the knowledge added is very similar to adding a lower bound `"t" <: T` into the context.

## Basic Use Case

First we look at the `depLikeFun` example. In the `if`-branch, returning `1` is allowed since after checking `str === "t"` the type of `T` can only be `"t"` or `"t" | "f"`. Thus, the caller will expect either a `number` or `number | boolean`, and thus it is safe to return the value `1`.

Note: The claim above that `T` can only be `"t"` or `"t" | "f"` is not quite true due to branded types. For example, `T` could also be the type `Branded`, defined as `type Branded = "t" & {_branded?: any}`. In this case the caller expects a value of type `unknown`, so returning `1` is also safe.

```ts
function depLikeFun<T extends "t" | "f">(str: T): F[T] {
  if (str === "t") {
    return 1; // no error
  } else {
    return true; // no error
  }
}
```

An example which does not occur for dependent functions, but does occur in dependent-type-like functions, is the following. The type `T` can be attributed to _multiple_ inputs, this possibility is what makes it unsafe to fully narrow the type parameter based on a check of the input `str`. However, the reasoning above still holds since the added knowledge is true regardless of how many inputs `T` is linked to.

```ts
function depLikeFun<T extends "t" | "f">(str: T, str2: T): F[T] {
  if (str === "t") {
    return 1; // no error
  } else {
    return true; // no error
  }
}
```

The extension is conservative, and behaviour of other cases should be the same as in 3.5. However, what might change is the error message users see when implementing dependent-type-like functions. In the situation below, instead of comparing `true` / `1` to `never`, they get compared against the simplified indexed access type within each branch. This is `number` in the then branch and `boolean` in the else branch.

```ts
function depLikeFun<T extends "t" | "f">(str: T): F[T] {
  if (str === "t") {
    return true; // Type 'true' is not assignable to type 'number'
  } else {
    return 1; // Type '1' is not assignable to type 'boolean'
  }
}
```

## Impact in Other Scenarios

The type `F[T]` can occur elsewhere in the function. This extension retains the normal TypeScript behaviour in those cases, and is only enabled when checking the return type of a function. In the following example we have a value of type `F[T]` as second input to the function. Within the then branch, this type should not be simplified to `number`, since it can actually be of type `boolean`. Checking the first input value does not give us any information regarding the second input value, and thus we cannot do any more simplification.

```ts
function depLikeFun<T extends "t" | "f">(str: T, ft: F[T]): F[T] {
  if (str === "t") {
    const n: number = ft; // Type 'F[T]' is not assignable to type 'number'.
    return 1;
  } else {
    return true;
  }
}

let x: boolean = false;
depLikeFun<"t" | "f">("t", x); // ft can be of type 'boolean'
```

## Transitive Type Parameters

TypeScript allows an indexed access with a type parameter which has a _direct_ transitive line to a correct bound. For example, it allows `function depLikeFun<T extends "t" | "f", B extends T>(str: B): F[B]`, but disallows `function depLikeFun<T extends "t", F extends "f", B extends T | F>(str: B): F[B]`.

In these situation it seems safe to let information flow through the transitive chain in both directions. For example, when checking an input of type `B`, we can add knowledge about `T`. And vice versa for checking an input of type `T` and an input of type `B`.

```ts
function depLikeFun<T extends "f" | "t", B extends T>(str: B): F[T] {
  if (str === "t") {
    return true; // no error
  } else {
    return 1; // no error
  }
}

function depLikeFun<T extends "f" | "t", B extends T>(str: T): F[B] {
  if (str === "t") {
    return true; // no error
  } else {
    return 1; // no error
  }
}
```

## Consistency with Conditional Types

TypeScript provides alternative means of creating type-level functions by using conditional types. Instead of creating the record type `F`, we can create the type constructor `F` which provides a similar mapping.

```ts
type F<A extends "t" | "f"> =
  A extends "t" ? number :
  A extends "f" ? boolean :
  never;
```

Which can be used as seen below.

```ts
function depLikeFun<T extends "t" | "f">(str: T): F<T> {
  if (str === "t") {
    return true;
  } else {
    return 1;
  }
}
```

This raises the question whether the addition of typechecking for dependent-type-like functions should be added for type level functions created with conditional types too, for consistency purposes. Two points worth noting is that: users were never able to implement this behaviour using conditional types (even pre-3.5), and, type level functions with conditional types are not restricted to a domain of string keys which makes things more complex. Nevertheless, we feel it is a point worth bringing up for discussion.

TODO: related issue: [#21879](https://github.com/microsoft/TypeScript/issues/21879), can this feature be used as a workaround for this issue?

## Behaviour with `any`

The result of instantiating a dependent-type-like function with the `any` type gives a result of `any`. This occurs, for example, when disabling `--strictNullChecks` and calling the function with `null`. Any behaviour related to interaction with `null`/`any` and dependent-type-like functions is supposed to be unchanged compared to 3.5.

## TODO

TODO: even more examples?

# Compiler Changes

In this section we roughly outline the suspected changes to the compiler needed to implement this extension.

- The main change is centered in the `getSimplifiedIndexedAccessType` function. When checking return types, the simplification process will now check when a generic parameter is used as `indexType`. Then, before the cache is consulted, it will look up checks of related variables with string literals in the control flow graph. The indexed access type is then simplified according to these checks as outlined in the proposal.
- To be able to check the control flow graph, it needs to be made accessible to the `getSimplifiedIndexedAccessType` function.
- The `getSimplifiedIndexedAccessType` must be informed to enable the additional simplification, the `checkReturnType` function will enable this behaviour when calling typechecking for the return type.

# Workaround

The current suggested workaround seems to be unsafe type assertions or overloaded signatures, both of which are unsafe features. Neither are satisfactory since the typechecker does not help in preventing programmer mistakes when implementing dependent-type-like functions.

# Related Suggestions

In this section we gather related suggestions which could be considered alternative solutions to this problem.

- extending the TypeScript syntax, such as a `oneof` generic constraint: [#25879](https://github.com/microsoft/TypeScript/issues/25879), [#27808](https://github.com/microsoft/TypeScript/issues/27808) or [#30284](https://github.com/microsoft/TypeScript/pull/30284)
- dependent types in TypeScript, which would have a huge impact on the compiler and is possibly out of scope for the TypeScript project
- this extension is a more refined idea based on previous ideas of narrowing types based on term-level checks such as [#21879](https://github.com/microsoft/TypeScript/issues/21879)

# Checklist

My suggestion meets these guidelines:

- [x] This wouldn't be a breaking change in existing TypeScript/JavaScript code
- [x] This wouldn't change the runtime behavior of existing JavaScript code
- [x] This could be implemented without emitting different JS based on the types of the expressions
- [x] This isn't a runtime feature (e.g. library functionality, non-ECMAScript syntax with JavaScript output, etc.)
- [x] This feature would agree with the rest of [TypeScript's Design Goals](https://github.com/Microsoft/TypeScript/wiki/TypeScript-Design-Goals).

Regarding bullet point 1: the goal of this proposal is to provide more _complete_ typechecking than 3.5, and thus we want to avoid breaking any code compared to 3.5.
