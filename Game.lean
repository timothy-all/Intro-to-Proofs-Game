import Game.Levels.EquivWorld
import Game.Levels.EquivWorld.EquivWorld_eg
import Game.Levels.ArgWorld
import Game.Levels.ArgWorld.ArgWorld_eg
import Game.Levels.QuantifierWorld
import Game.Levels.QuantifierWorld.QuantifierWorld_eg
import Game.Levels.SetWorld
import Game.Levels.SetWorld.SetWorld_eg
import Game.Levels.PfWorld
import Game.Levels.PfWorld.PfWorld_eg
import Game.Levels.RelationWorld
import Game.Levels.RelationWorld.RelationWorldExamples
import Game.Levels.FunctionWorld
--import Game.Levels.FunctionWorldExamples

--import Game.Levels.LeanFunctionWorld
--import Game.Levels.InductionWorld
--import Game.Levels.CardinalityWorld

-- Here's what we'll put on the title screen
Title "Intro to Proofs Game"
Introduction
"
# **The Intro to Proofs Game**
Welcome to **The Intro to Proofs Game**. The object of this game is to help you navigate the course MA276. Most proofs we do in class (or that are assigned as homework) are in this game! In order to play, we'll need to learn a little bit about L∃∀N ...

### **What is L∃∀N**

Lean (stylized as L∃∀N) is a proof assistant and programming language -- this means that it helps to codify mathematical proofs. As we write proofs of our claims (or theorems) in Lean, a terminal will dynamically report our givens and goals so we know where we are in the proof. As goals get cleared, we'll stock an inventory of rigorous, *machine-verified* proofs so we'll know that our proofs are correct!

### **How to play?**

The world map is in the center pane. Individual world-levels are the pearls encircling the worlds. Once you've cleared a level, you can move onto the next. The same thing is true with worlds. You can replay any level by navigating to it from the world map. **Start** with **Logical Equivalence World**.
"

Info "
This game was written by Drs. Timothy All and Tyler Billingsley at Rose-Hulman Institute of Technology.

This is version 1.0.
"

--Dependency SetWorld → PfWorld

/-! Information to be displayed on the servers landing page. -/
Languages "en"
CaptionShort "Intro to Proofs Game"
CaptionLong "This game is designed to accompany students through MA276."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
