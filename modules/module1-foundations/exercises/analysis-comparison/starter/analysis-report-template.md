# Analysis Classification Exercise

## Instructions
For each code snippet in `code-samples.md`, fill in the table below.

**Objective categories:** Correctness, Security, Performance
**Detection method:** Static, Dynamic, Both

---

| Snippet | Issue Description | Objective | Detection Method | Explanation |
|---------|-------------------|-----------|-----------------|-------------|
| 1 |SQL injection via string concatenation|Security|Static|Direct concatenation of user input into SQL is unsafe and detectable by scanning for unsafe query construction.|
| 2 |Unreachable code after `return`|Correctness|Static|The `console.log` will never run; static analysis can see unreachable statements.|
| 3 |Division by zero if list is empty|Correctness|Dynamic|Only occurs at runtime when `numbers` is empty; static tools can warn, but runtime needed to confirm.|
| 4 |Missing null terminator → buffer overflow|Correctness/Security|Static|Function copies characters but never writes '\0', causing undefined behavior and potential overflow.|
| 5 |Off‑by‑one error (`<=` instead of `<`)|Correctness|Static|Loop accesses `items[items.length]`, which is out of bounds.|
| 6 |Exponential recursion → severe slowdown|Performance|Both(Static & Dynamic)|Static tools can warn about naive recursion; runtime shows actual slowdown.|
| 7 |Resource leak: file never closed|Correctness/Performance|Static|Missing `close()` is visible statically; may cause runtime exhaustion.|
| 8 |Command injection via `os.system`|Security|Static|Direct concatenation of user input into shell commands is unsafe.|
| 9 |Memory leak / unbounded cache growth|Performance|Dynamic|Static tools can warn, but the leak manifests only over time at runtime.|
| 10 |Unreachable code after `return`|Correctness|Static|`result.clear()` will never execute.|
| 11 |Inconsistent state if exception occurs mid‑transfer|Correctness|Dynamic|Requires runtime behavior to expose inconsistent account states.|
| 12 |Inefficient O(n²) search|Performance|Static|Nested loops for a simple search are detectable by static analysis.|
| 13 |XSS vulnerability via `innerHTML`|Security|Static|Direct insertion of untrusted input into HTML is unsafe.|
| 14 |Division by zero if divisor is zero|Correctness|Dynamic|Only fails when divisor is zero at runtime.|
| 15 |Returning pointer to local stack memory|Correctness/Security|Static|Stack memory becomes invalid after function returns; statically detectable.|

---

## Summary Questions

### How many snippets had Correctness issues? 9 snippets
### How many had Security issues? 4 snippets
### How many had Performance issues? 4 snippets

### Which issues are best caught by static analysis? Why?
Static analysis is best at catching structural code problems, unsafe patterns, resource leaks, returning invalid memory, and inefficient algorithms because these are visible directly from the code with execution.

### Which issues require dynamic analysis? Why?
Dynamic analysis is needed when the problem depends on runtime values, state evolves, exceptions, or timing affects correctness, and performance degradation emerges only under load because these only manifest when the program runs with real inputs and real system behavior.
