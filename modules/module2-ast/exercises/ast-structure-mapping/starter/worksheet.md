# AST Structure Mapping Worksheet

## Instructions
For each snippet, first draw the AST by hand, then verify with the visualizer.

---

## Snippet 1: `result = (2 + 3) * 4`

### Hand-drawn AST
<!-- Draw or describe the tree structure here -->
  Assign("result")
        |
       (*)
     /     \
   (+)      4
   / \
  2   3
### Visualizer output matches? (yes/no): yess

### Node types used:
- Assign
- BinOp
- IntLit
---

## Snippet 2: If-Else
```python
if x > 0:
    y = x + 1
else:
    y = 0
```

### Hand-drawn AST
If
├── BinOp(>)
│   ├── Var("x")
│   └── IntLit(0)
├── Then
│   └── Assign("y")
│       └── BinOp(+)
│           ├── Var("x")
│           └── IntLit(1)
└── Else
    └── Assign("y")
        └── IntLit(0)

### Key observation about the If node's children:
- The `If` node has three parts:
    - Condition
    - Then branch
    - Else branch 

---

## Snippet 3: Function Definition
```python
def greet(name):
    message = "Hello, " + name
    return message
```

### Hand-drawn AST
Assign("message")
  └── BinOp(+)
      ├── "Hello, "
      └── Var("name")

Return
  └── Var("message")

### How is the function parameter represented?
Var("name")

---

## Snippet 4: For Loop
```python
total = 0
for i in range(10):
    if i % 2 == 0:
        total = total + i
```

### Hand-drawn AST
Assign("total")
  └── IntLit(0)

For / While-like structure
├── Var("i") in Call("range", [10])
└── Body
    └── If
        ├── BinOp(==)
        │   ├── BinOp(%)
        │   │   ├── Var("i")
        │   │   └── IntLit(2)
        │   └── IntLit(0)
        └── Then
            └── Assign("total")
                └── BinOp(+)
                    ├── Var("total")
                    └── Var("i")

### What is the nesting depth of the innermost node?
Count levels:
- For loop
- If
- Equality `==`
- Mod `%`
- Variable/literal

---

## Reflection Questions

### 1. How does operator precedence appear in the AST?
Operator precedence is represented by tree structure, not symbols.
- Higher-precedence operations are deeper in the tree
- Example: `(2+3)*4` -> `+` is nested inside `*`

### 2. What syntactic elements (from the source code) are NOT in the AST?
The AST removes surface-level syntax like:
- Parentheses
- Indentation
- Commas
- Semicolons
- Keywords like `def`, `for` (often abstracted)

### 3. How would you use the AST to find all variable assignments in a program?

Traverse the AST and look for:
`Assign(var,expr)`

Algorithm:
1. Walk through all statements
2. When you see `Assign`, record the variable
3. Continue recursively into nested blocks
