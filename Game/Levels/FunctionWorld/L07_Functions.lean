import Game.Levels.FunctionWorld.L06_Functions


World "FunctionWorld"
Level 7

Title "Functions 7"

Introduction "## **Level 7 : Surjective (onto) Functions**

Now let's do a straightforward onto example. Fortunately, onto is quite a bit simpler to work with in Lean - 🔍 check your inventory for details."

/-- If $f$ and $g$ are functions such that $g ∘ f$ is surjective, then $g$ is surjective. -/
Statement {u v w: Type*} (f: Rel u v) (hf: isFunction f) (g: Rel v w) (hg: isFunction g) (hgfs: isSurjective (g ∘ f)) : isSurjective g := by
  Hint "Let's grab our arbitrary codomain element: 👉 `intro c`."
  intro c
  Hint "We have to find `a` such that `g a c`. Well, `g ∘ f` is surjective, so `g ∘ f` must map something to `c`; let's grab it: 👉 ```obtain ⟨a,gfac⟩ := hgfs c``` This *plugs in* `c` to the surjective condition, allowing us to unpack *what maps to c* by using `obtain`."
  obtain ⟨a,gfac⟩ := hgfs c
  Hint "What `g` itself maps to `c` is wrapped up in the existentially-quantified `gfac` now. Use `obtain` to grab it and take it from here!"
  obtain ⟨b,hb⟩ := gfac
  --Line below unpacks surjectivity condition & composite all at once
  --obtain ⟨a,⟨b,⟨hab,hbc⟩⟩⟩ := hgfs c
  exist b
  exact hb.right


Conclusion "### **💡 Pro-tip**

The game led you through doing two `obtain`s in a row to make the proof easy, but you can do them both at once via nesting! Go back in and try this: `obtain ⟨a,⟨b,⟨hfab,hgbc⟩⟩⟩ := hgfs c`."

NewDefinition isSurjective
