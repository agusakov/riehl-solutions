import category_theory.category -- this transitively imports
-- category_theory.category
-- category_theory.functor
-- category_theory.natural_transformation
import category_theory.isomorphism
import tactic

open category_theory

universes v u

variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

--variables {W X Y Z : C}
--variables (f : X ⟶ Y) (g : Y ⟶ X) (h : Y ⟶ X)

/-Exercise 1.1.i-/ 
/-(i) Show that a morphism can have at most one inverse isomorphism-/

lemma at_most_one_inv {X Y : C} (f : X ⟶ Y) (g : Y ≅ X): 
f ≫ g.hom = 𝟙 X → f = g.inv :=
begin
    intro h1,
    calc f = f ≫ 𝟙 Y :
        by {rw [category.comp_id]}
        ... = f ≫ g.hom ≫ g.inv :
        by {rw [iso.hom_inv_id]}
        ... = 𝟙 X ≫ g.inv:
        by {symmetry' at h1, rw [h1, category.assoc]}
        ... = g.inv:
        by {rw [category.id_comp]}
end

/-(ii) Consider a morphism f: x ⟶ y. Show that if there exists a pair of morphisms
g, h : y ⟶ x so that gf = 𝟙 x and fg = 𝟙 y, then g = h and f is an isomorphism.-/ 

lemma left_right_inv_eq {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) (h : Y ⟶ X) : 
f ≫ g = 𝟙 X ∧ h ≫ f = 𝟙 Y → g = h :=
begin
    intro h1,
    cases h1 with hgx hhy,
    calc g = 𝟙 Y ≫ g :
    by {rw [category.id_comp]}
    ... = h ≫ f ≫ g :
    by {symmetry' at hhy, rw [hhy, category.assoc]}
    ... = h ≫ 𝟙 X :
    by {rw [hgx]}
    ... = h :
    by {rw [category.comp_id]}
end

def left_right_inv_iso {X Y : C} (f : X ⟶ Y) (g : Y ≅ X) (h : Y ≅ X) : 
f ≫ g.hom = 𝟙 X ∧ h.hom ≫ f = 𝟙 Y → is_iso f :=
begin
    intro h1,
    cases h1 with hgx hhy,
    have hg : g.hom = h.hom :=
        -- not proud of this one
        by {apply left_right_inv_eq, split, exact hgx, exact hhy},
    rw hg at hgx,
    have h2 : f = h.inv :=
        by {apply at_most_one_inv, exact hgx},
    rw h2,
    apply is_iso.of_iso_inverse,
end