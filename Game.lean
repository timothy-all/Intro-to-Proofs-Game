--import Game.Levels.TimWorld
--import Game.Levels.TylerWorld
import Game.Levels.EquivWorld
import Game.Levels.EquivWorld.EquivWorld_eg
import Game.Levels.ArgWorld
import Game.Levels.ArgWorld.ArgWorld_eg
--import Game.Levels.QuantifierWorld
--import Game.Levels.QuantifierWorld.QuantifierWorld_eg
--import Game.Levels.SetWorld
--import Game.Levels.SetWorld.SetWorld_eg
--import Game.Levels.RelationWorld
--import Game.Levels.RelationWorld.RelationWorldExamples
--import Game.Levels.FunctionWorld
--import Game.Levels.FunctionWorldExamples
--import Game.Levels.LeanFunctionWorld
--import Game.Levels.InductionWorld
--import Game.Levels.CardinalityWorld
--import Game.Levels.PfWorld
--import Game.Levels.PfWorld.PfWorld_eg

-- Here's what we'll put on the title screen
Title "Intro to Proofs Game"
Introduction
"
# **Welcome**
The *Intro to Proofs Game* should do some really really neat stuff.
"

Info "
Here you can put additional information about the game. It is accessible
from the starting through the drop-down menu.

For example: Game version, Credits, Link to Github and Zulip, etc.

Use **markdown**.
"

/-! Information to be displayed on the servers landing page. -/
Languages "en"
CaptionShort "Game Template"
CaptionLong "You should use this game as a template for your own game and add your own levels."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
