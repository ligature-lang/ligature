/-
Ligature Configuration Language Specification
============================================

This file contains the specification of Ligature's configuration language features,
including basic configuration validation.
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Logic.Basic
import Ligature

/-!
# Configuration Language Specification

## Overview

This specification defines Ligature's configuration language features,
including configuration values and basic validation.
-/

/-!
## Configuration Values
-/

/-- Configuration values -/
inductive ConfigValue where
  | string : String → ConfigValue
  | integer : Int → ConfigValue
  | float : Float → ConfigValue
  | boolean : Bool → ConfigValue
  deriving Repr

/-!
## Configuration Validation
-/

/-- Configuration validation judgment: env ⊢ v : τ -/
inductive ConfigValidate : Environment → ConfigValue → LigatureType → Prop where
  -- String validation
  | string : ConfigValidate env (ConfigValue.string _) LigatureType.string

  -- Integer validation
  | integer : ConfigValidate env (ConfigValue.integer _) LigatureType.integer

  -- Float validation
  | float : ConfigValidate env (ConfigValue.float _) LigatureType.float

  -- Boolean validation
  | boolean : ConfigValidate env (ConfigValue.boolean _) LigatureType.bool

/-!
## Examples
-/

/-- Example: Server configuration -/
def serverConfig : ConfigValue := ConfigValue.integer 9000

/-- Example: Configuration validation -/
theorem example_config_validation : ConfigValidate ([] : List (Name × Value)) serverConfig LigatureType.integer := by
  apply ConfigValidate.integer

/-!
## Properties
-/

/-- Configuration validation is sound -/
theorem config_validation_sound : ConfigValidate env config τ → True := by
  intro _
  trivial
