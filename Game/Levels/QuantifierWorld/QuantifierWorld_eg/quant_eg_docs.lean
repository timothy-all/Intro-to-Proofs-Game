import GameServer

/--
The tactic `rcases` is used to destructure hypotheses or expressions. General usage looks like `rcases h with patt` where `patt` is a pattern matched against `h`. For example, suppose `h : (a ∧ b ∧ c) ∨ (d ∧ e)`. Usual usage might be
```
rcases h with ⟨ha, hb, hc⟩ | ⟨ hd, he⟩
```
In this case, our goal would be split in two. The first goal would contain the hypotheses `ha : a`, `hb : b`, and `hc : c`. The second goal would contain the hypotheses `hd : d` and `he : e`. If a hypothesis will be irrelevant, we might choose to not explicitly name it by using `_`.
### **💡 Pro-tip**
There are scenarios where we may wish to **keep** the original hypothesis `h` in addition to any destructuring done by `rcases`. Usual usage might be
```
rcases hpf : h with ⟨ ha, hb, hc ⟩
```
What does `hpf` contain? The formal proof that `h` can be destructured into `⟨ ha, hb, hc⟩`. Typically, we won't need `hpf`.
### **⌨ Typesetting-tip**
There's a difference between the angled brackets `⟨ ⟩` and the relations `< >`. In order to produce the *angled brackets* use `\\langle` and `\\rangle`.
-/
TacticDoc rcases


/--
Forall distributes over ands
-/
TheoremDoc Forall_and as "QUA: Forall_and"
