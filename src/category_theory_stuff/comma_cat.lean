import category_theory.functor_category -- this transitively imports
-- category_theory.category
-- category_theory.functor
-- category_theory.natural_transformation
open category_theory

section comma_cat

universes v u  -- the order matters (see below)

variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞


end comma_cat