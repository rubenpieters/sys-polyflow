# Search Terms

generic indexed access type dependent function

# Suggestion

TypeScript does not provide dependent types, but combining various features such as unions, literal types and indexed access types we can obtain fairly similar behaviour from the caller point of view. Hence the name: dependent-type_-like_ functions. Unfortunately, the implementer of such functions is faced with either the possibility of unsoundness (pre 3.5) or forced to use unsound assertions (post 3.5).

This suggestion proposes an addition to the typechecking part of TypeScript, which aids the programmer in writing dependent-type-like functions. The main attractive point of this suggestion is that it does not introduce any additional syntax, and thus is not a breaking change with regards to 3.5.

# Use Cases

The main use case is that of a dependent-type-like function. The `depLikeFun` example is a minimalistic scenario showcasing the main idea. In this example, we have the `depLikeFun` function which returns `number` when its input is of type `"t"` and `boolean` when its input is of type `"f"`.

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

This pattern occurs in various places, such as the [TypeScript dom bindings](https://github.com/microsoft/TypeScript/blob/ca00b3248b1af2263d0223d68e792b7ca39abcab/lib/lib.dom.d.ts#L11050), in issues such as [#31672](https://github.com/microsoft/TypeScript/issues/31672) and [#32698](https://github.com/microsoft/TypeScript/issues/32698), or on [stackoverflow questions](https://stackoverflow.com/questions/56479117/how-to-fix-ts2322-when-using-a-case-switch-and-generics).

# Problem

The problem lies in the implementation of the function. The pre-3.5 behaviour allowed unsoundness in these type of functions. TypeScript checked the return value against the union of the possibilities, which is `number | boolean`. However, this is unsound since the caller expects different behaviour based on the function signature.

```ts
// pre-3.5
function depLikeFun<T extends "t" | "f">(str: T): F[T] {
  if (str === "t") {
    return true; // should be error
  } else {
    return 1; // should be error
  }
}

depFun("t"); // has type number, but is actually a boolean
depFun("f"); // has type boolean, but is actually a number
```

The post-3.5 behaviour also isn't satisfactory for this use case. It disallows the `depLikeFun` to be implemented without any unsafe type assertions. By [#30769](https://github.com/microsoft/TypeScript/issues/30739), the `return` calls are considered writes to the result of the function. This means that the result type `F[T]` is checked against the _intersection_ of the possibilities, which is `number & boolean` and thus `never`. 

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

# Examples

In a dependently typed language `depLikeFun` would be modeled as `function depFun(str: "t" | "f"): F[str]`. There are meaningful differences between depending on the actual _value_ of the input versus the _type_ of an input. This distinction makes this issue somewhat tricky to solve. In this section we showcase the expected behaviour of the addition on certain representative examples.

First we look at the `depLikeFun` example. In the `if`-branch, returning `1` is allowed since after checking `str === "t"` the type of `T` can only be `"t"` or `"t" | "f"`. Thus, the caller will expect either a `number` or `number | boolean`, and thus it is safe to return the value `1`.

Note: The claim above that `T` can only be `"t"` or `"t" | "f"` is not true due to branded types. For example, `T` could also be the type `Branded`, defined as `type Branded = "t" & {_branded?: any}`. In this case the caller expects a value of type `unknown`, so returning `1` is also safe.

```ts
function depLikeFun<T extends "t" | "f">(str: T): F[T] {
  if (str === "t") {
    return 1; // no error
  } else {
    return true; // no error
  }
}
```

An example which does not occur for dependent functions, but does occur in dependent-type-like functions, is the following. The type `T` can be attributed to _multiple_ inputs, which makes it unsafe to fully narrow the type parameter based on a check of the input `str`. However, the reasoning above is not dependent on any narrowing and still holds.

```ts
function depLikeFun<T extends "t" | "f">(str: T, str2: T): F[T] {
  if (str === "t") {
    return 1; // no error
  } else {
    return true; // no error
  }
}
```

TODO: investigate more examples? Look at more complicated scenarios?

# Workaround

The current suggested workaround seems to be unsafe type assertions, or overloaded signatures which is also unsafe. Neither are satisfactory since the typechecker does not help in preventing programmer mistakes when implementing dependent-type-like functions.

# Related Suggestions

In this section we gather related suggestions which could be considered alternative solutions to this problem.

- extending the TypeScript syntax, such as a `oneof` generic constraint: [#25879](https://github.com/microsoft/TypeScript/issues/25879), [#27808](https://github.com/microsoft/TypeScript/issues/27808) or [#30284](https://github.com/microsoft/TypeScript/pull/30284)
- dependent types in TypeScript, which seems out of scope for the TypeScript project

# Checklist

My suggestion meets these guidelines:

- [x] This wouldn't be a breaking change in existing TypeScript/JavaScript code
- [x] This wouldn't change the runtime behavior of existing JavaScript code
- [x] This could be implemented without emitting different JS based on the types of the expressions
- [x] This isn't a runtime feature (e.g. library functionality, non-ECMAScript syntax with JavaScript output, etc.)
- [x] This feature would agree with the rest of [TypeScript's Design Goals](https://github.com/Microsoft/TypeScript/wiki/TypeScript-Design-Goals).

Regarding bullet point 1: the goal of this proposal is to provide more _complete_ typechecking than 3.5, and thus we want to avoid breaking any code compared to 3.5.
