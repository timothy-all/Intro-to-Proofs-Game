import Game.Levels.EquivWorld.L03_equiv

World "EquivWorld"
Level 4

Title "Targeted Rewrites"

Introduction "
## **Level 4**
The goal of this level is intuitively clear. But in order to prove it formally, we'll need some **targeted rewrites** with the **Associative Law** for `∧`, called `And_assoc`. 🔍 Check out the entry for `And_assoc` in the **Theorems** tab. 👉 To get started, try:
```
rw[And_assoc]
```
"

set_option pp.parens true



Statement (P Q R S : Prop) : (P ∧ Q) ∧ (R ∧ S) ↔ (P ∧ S) ∧ (R ∧ Q) := by
  rw[And_assoc]
  Hint "**Here's what happend:** `And_assoc` was applied to the **first instance** encountered where it could be applied. Specifically, Lean searched for the first instance of
  ```
  (_ ∧ _) ∧ _
  ```
  where the underscores are wildcards. The first underscore was matched to `P`, the second to `Q` and the third to `R ∧ S`. Lean then applied `And_assoc` (from ***left-to-right***) to this instance. In particular, the left-hand side of our goal is now:
    ```
    P ∧ (Q ∧ (R ∧ S))
    ```
  👉 Now try:
    ```
    rw[← And_assoc Q]
    ```
    This will apply the associative law *in reverse*...
    ### **⌨ Typesetting Tip**
    To prety print the left arrow `←` use `\\left`. You can also use `<-` if you're not interested in pretty printing.
    "
  rw[← And_assoc Q]
  Hint "**Here's what happened:** Lean searched for the **first instance** of
    ```
    Q ∧ (_ ∧ _)
    ```
    where the underscores are wildcards. The first underscore was matched with `R`, the second with `S`. Lean then applied `← And_assoc` (from ***right-to-left***) to this instance. In particular, Lean substituted `(Q ∧ R) ∧ S` for `Q ∧ (R ∧ S)`.

    Now we'd like to **commute** the expression `(Q ∧ R) ∧ S` to get `S ∧ (Q ∧ R)`. 👉 We can accomplish this with either:
    ```
    rw[And_comm (Q ∧ R)]
    ```
    or
    ```
    rw[And_comm (Q ∧ R) S]
    ```
    or even
    ```
    rw[And_comm _ S]
    ```
    This last form is slightly dangerous in this case though; 🤔 can you tell why?
    ### **⌨ Typesetting Tip**
  In order to pretty-print symbols like `∧` use `\\wedge` or `\\and`."
  rw[And_comm (Q ∧ R)]
  Hint "Great, we're almost home. Try to to finish this level off on your own."
  rw[← And_assoc]
  rw[And_comm Q]


Conclusion "
"

NewTheorem And_assoc And_comm
