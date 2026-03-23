# Analysis Report: Calculator Bugs

## Student Name: Arnav Vasa
## Date: 3/12/26

---

## Part 1: Static Analysis Findings (ESLint)

Run `npx eslint calculator.js` and record all findings below.

| # | Line | Rule | Description | Severity |
|---|------|------|-------------|----------|
| 1 |14|no-undef|'reslt' is not defined|Error|
| 2 |20|no-unreachable|Unreachable console.log after return|Warning|
| 3 |28|no-fallthrough|Switch case falls through from "add" to "subtract"|Warning|
| 4 |63|no-unused-vars|Variable temp is assigned but never used|Warning|
| 5 |73|no-constant-condition|if (true) is a constant condition|Warning|

**Total static analysis issues found:** 5

---

## Part 2: Dynamic Analysis Findings (Test Suite)

Run `node test-calculator.js` and record all test failures below.

| # | Test Name | Error Message | Root Cause |
|---|-----------|---------------|------------|
| 1 |add(2, 3) should be 5|reslt is not defined|Typo in add() (reslt instead of b)|
| 2 |add(-1, 1) should be 0|reslt is not defined|Same undefined variable bug in add()|
| 3 |divide(10, 0) should throw or return Infinity gracefully|Division by zero should be handled, got Infinity|No check for division by zero|
| 4 |calculate('add', 10, 5) should be 15|expected 15, got 5|Switch fallthrough overwrites result with subtraction|
| 5 |factorial(-1) should handle negative input|Infinite recursion detected -- needs base case for negative numbers|Missing base case for negative values|
| 6 |absolute(5) should be 5|expected 5, got -5|Constant condition (if (true)) always negates|
| 7 |absolute(-3) should be 3|expected 3, got 3 OR passes depending on interpretation|Logic is incorrect but coincidentally passes for negative input|

**Total dynamic analysis issues found:** 6

---

## Part 3: Comparison

### Which bugs did ONLY static analysis catch?
<!-- List bugs found by ESLint but NOT by running tests -->

1. Unreachable code in subtract() (code after return)
2. Unused variable temp in power()
3. Constant condition in absolute() (if (true))

### Which bugs did ONLY dynamic analysis catch?
<!-- List bugs found by tests but NOT by ESLint -->

1. Division by zero issue in divide()
2. Infinite recursion in factorial() for negative input

### Which bugs were found by BOTH approaches?
<!-- List bugs caught by both ESLint and test failures -->

1. Undefined variable reslt in add()
2. Switch fallthrough in calculate() causing incorrect results

---

## Part 4: Reflection

### Why can't static analysis catch all bugs?
Static analysis does not execute the code, so it cannot detect 
runtime issues such as incorrect outputs, infinite recursion, or 
edge cases like division by zero. It focuses on code structure 
and patterns rather than actual program behavior.


### Why can't dynamic analysis catch all bugs?
Dynamic analysis depends on the test cases provided, so it only 
detects bugs in the parts of the code that are executed. If 
certain edge cases or scenarios are not tested, those bugs will 
remain undetected.


### When would you prioritize one approach over the other?
Static analysis is best used early in development to catch syntax 
errors and enforce coding standards quickly. Dynamic analysis is 
more useful when verifying correctness and handling real-world 
inputs. In practice, both approaches should be used together for 
thorough testing.
