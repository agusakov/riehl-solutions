import category_theory.category -- this transitively imports
-- category_theory.category
-- category_theory.functor
-- category_theory.natural_transformation
import category_theory.isomorphism
import tactic

open category_theory

universes v v₂ u u₂

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

/-Exercise 1.1.ii-/
/-Let C be a category. Show that the collection of isomorphisms in C defines a 
subcategory, the maximal groupoid inside C.-/
--To do:
-- define objects (just need to show 𝟙 C is iso and I think all the objects of C follow?)
-- define morphisms (just isomorphisms of C)
-- show that all morphisms have dom/cod (spoiler: they do, we have all objects)
-- identity morphisms (again, they are isomorphisms)
-- closure of composite morphisms - probably the only hard part in Lean

def identity_is_iso {X : C} : is_iso (𝟙 X) :=
begin
    have hinv : 𝟙 X ≫ 𝟙 X = 𝟙 X :=
        by {rw [category.id_comp]},
    sorry,
end
-- need f.hom ≫ g.hom ≫ g.inv ≫ f.inv = 𝟙 X
def hom_comp_is_iso {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z) :
is_iso (f.hom ≫ g.hom) := 
begin
    have hfx : 𝟙 X = f.hom ≫ f.inv :=
        by {sorry},
    have hfy : 𝟙 Y = f.inv ≫ f.hom := 
        by {sorry},
    have hgy : 𝟙 Y = g.hom ≫ g.inv :=
        by {sorry},
    have hgz : 𝟙 Z = g.inv ≫ g.hom :=
        by {sorry},
    
    have hfin1 : 𝟙 X = f.hom ≫ g.hom ≫ g.inv ≫ f.inv :=
        calc 𝟙 X = f.hom ≫ f.inv :
            by {sorry}
        ... = f.hom ≫ 𝟙 Y ≫ f.inv :
            by {sorry}
        ... = f.hom ≫ g.hom ≫ g.inv ≫ f.inv :
            by {sorry},
    sorry,
end
-- incredibly inefficient. not even gonna bother with this.
-- figure out how to rephrase.

def inv_comp_is_iso {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z) :
is_iso (g.inv ≫ f.inv) := 
begin
    sorry,
end


/-Exercise 1.1.iii For any category C and any object A ∈ C, show that:-/

/-(i) There is a category A/C whose objects are morphisms f : A ⟶ X
with domain A and in which a morphism from f : A ⟶ X to g : A ⟶ Y
is a map h : X ⟶ Y such that g = hf.-/

variables (AC : Type v) [A𝒞 : category.{v} AC]
include A𝒞
--goal:
/-
class category_struct (obj : Type u)
extends has_hom.{v} obj : Type (max u (v+1)) :=
(id       : Π X : obj, hom X X)
(comp     : Π {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z))

class category (obj : Type u)
extends category_struct.{v} obj : Type (max u (v+1)) :=
(id_comp' : ∀ {X Y : obj} (f : hom X Y), 𝟙 X ≫ f = f . obviously)
(comp_id' : ∀ {X Y : obj} (f : hom X Y), f ≫ 𝟙 Y = f . obviously)
(assoc'   : ∀ {W X Y Z : obj} (f : hom W X) (g : hom X Y) (h : hom Y Z),
  (f ≫ g) ≫ h = f ≫ (g ≫ h) . obviously)-/
class has_slice_hom (obj : Type v) : Type (max v (v+1)) :=
(hom : obj → obj → Type v)

--ugh
/-class slice_struct (A : C) (obj : Type v) extends has_slice_hom.{v} obj : Type (max v (v+1)) :=
(id : Π {X : C}, (A ⟶ X) : obj, hom (A ⟶ X) (A ⟶ X). obviously)
(comp : Π {(A ⟶ X) (A ⟶ Y) (A ⟶ Z): AC}, (A ⟶ X) ⟶ (A ⟶ Y))-/


/-class slice (obj : Type u) extends category.{v} obj : Type (max u (v+1)) :=
(inv       : Π {X Y : obj}, (X ⟶ Y) → (Y ⟶ X))
(inv_comp' : ∀ {X Y : obj} (f : X ⟶ Y), comp (inv f) f = id Y . obviously)
(comp_inv' : ∀ {X Y : obj} (f : X ⟶ Y), comp f (inv f) = id X . obviously)-/