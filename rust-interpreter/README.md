# An Interpreter for the Monkey Programming Language
An interpreter written in Rust for the monkey programming language described in the book "Writing An Interpreter In Go" (https://interpreterbook.com).

## Installation
You can try the interpreter in most modern web-browsers that support web assembly at https://arjan-bal.github.io/monkey-interpreter-wasm.

Alternatively, to build and run the interpreter locally, install the rust compiler and build tool by following instruction on the [official website](https://www.rust-lang.org/tools/install). Then from the root of the cloned project run the following:
```bash
cd ./rust-interpreter
cargo run
```


## Running unit tests
From the root of the repository run the following commands:
```bash
cd ./rust-interpreter
cargo test
```

## Monkey Syntax
Here the main features of the monkey programming language with examples. Monkey is whitespace insensitive.

### Variables
Monkey is a dynamically typed language. Variables in Monkey are immutable. To override the values, you need to declare a variable with the same name. Monkey supports the following data types:
* Booleans: Eg: `let valid = true;`
* Integers: Integers are 64 bit and signed. Eg: `let a = 10; let b = -23;`
* Strings: Eg: `let myName = "Arjan";`
* Functions: Yes, functions can be stored in variables and passed as parameters to other functions! Look at the section on function below. Eg: `let add1 = fn (x) { x + 1; };`
* Arrays: Arrays store a list of other variables. Eg: `let arr = ["dog", 1, fn (x) { x + 1; }, false]; let a0 = arr[0];`
* Hashes: Also known as hashmaps or dictionaries in other languages. They allow only strings, booleans and integers as keys. The values can be any variable. Eg: `let person = { "name": "jake", "score": 12, yes: no, 2: 5 }; let candidateName = person["name"];`
* null: This represents values that don't exist. Eg: `let arr = [1, 2]; let a = arr[100];` Here a will be `null`.

### Conditionals
If/else statements can be written as follows:
```
let score = 49;
let pass_marks = 51;
let result = if (score > pass_marks) {
  "pass"
} else {
  "fail"
};
```

### Functions
Functions can take a fixed number of expressions/variables as parameters and return a single value using the `return` keyword. Eg:
```
let add = fn (a, b) {
  return a + b;
}

let sum = add(2, 2);
let message = add("hello ", "world");
```
If functions don't have an explicit return statement, the result of the last statement is returned as the implicit return values. Eg, the same add function can be written as:
```
let add = fn (a, b) {
  a + b;
};
```
or
```
let add = fn (a, b) {
  a + b
};
```

### Closures
Functions can capture values in the enclosing scope. Eg:
```
let multiplier = fn (k) {
  return fn (val) {
    val * k
  }
};

let double = multiplier(2);
let four = double(2);
```

The value returned by the last statement is `10`.
```
let a = 4;
let return_a = fn () {
  a
};
let a = 10;
return_a();
```

### Higher order functions
In Monkey, we can pass functions as arguments to other functions.

```
let values = [1, 2, 3, 4, 5];
let predicate = fn (x) {
  x < 3
};

let filter_predicate = fn (predicate) {
  let filter = fn (arr, result, index) {
    let new_result = result;
    if (len(arr) < index + 1) {
      return new_result;
    }
    if (predicate(arr[index])) {
      let new_result = push(new_result, arr[index]);
    }
    filter(arr, new_result, index + 1)
  };
  filter
}
filter_predicate(predicate)(values, [], 0);
```
The value of the last statement is `[1, 2]` since those are the only elements that satisfy the predicate.

Here's another example that implements the map function for arrays using some builtin functions that are described later.
```
let map = fn(arr, f) {
  let iter = fn(arr, accumulated) {
    if (len(arr) == 0) {
      accumulated
    } else {
      iter(rest(arr), push(accumulated, f(first(arr))));
    }
  };
  iter(arr, []);
};

let a = [1, 2, 3, 4];
let double = fn(x) { x * 2 };
map(a, double);
```
The value of the last line is `[2, 4, 6, 8]`.

Here's an implementation for a reduce function.
```
let reduce = fn(arr, initial, f) {
  let iter = fn(arr, result) {
    if (len(arr) == 0) {
      result
    } else {
      iter(rest(arr), f(result, first(arr)));
    }
  };
  iter(arr, initial);
};

let sum = fn(arr) {
  reduce(arr, 0, fn(initial, el) { initial + el });
};

sum([1, 2, 3, 4, 5]);
```
The result of the list line is `15`.

### Builtin functions
Monkey has the following builtin functions:
* len(x): This takes a string or an array as a argument and returns its length. Eg: `let size = len([1, true, false]); let size = len("abc");`
* first: Returns the first element of an array. Eg: `let one = first([1, 2, 3]);`
* last(arr): Returns the last element of an array. Eg: `let three = last([1, 2, 3]);`
* rest(arr): Returns a sub-array that contains all the elements except the first. Eg: `let arr1 = rest([1, 2, 3]); let arr2 = [2, 3];`. Both `arr1` and `arr2` has the same values.
* push(arr, x): Returns an array with a new values added to the original array. Note that this doesn't change the original array, but returns an entirely new array. Eg: `let arr = push([1, 2], 3);`.  The array would have the value `[1, 2, 3]`.