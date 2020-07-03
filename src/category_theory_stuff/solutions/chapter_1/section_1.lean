import category_theory.category -- this transitively imports
-- category_theory.category
-- category_theory.functor
-- category_theory.natural_transformation
import category_theory.isomorphism
import category_theory.groupoid
import tactic

open category_theory

universes v u

variables (C : Type u) [category.{v} C]

--variables {W X Y Z : C}
--variables (f : X ⟶ Y) (g : Y ⟶ X) (h : Y ⟶ X)

/-Exercise 1.1.i-/ 
/-(i) Show that a morphism can have at most one inverse isomorphism-/

lemma at_most_one_inv {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) [is_iso g]: 
f ≫ g = 𝟙 X → f = inv g:=
begin
    intro h1,
    calc f = f ≫ 𝟙 Y :
        by {rw [category.comp_id]}
        ... = f ≫ g ≫ inv g :
        by {rw [is_iso.hom_inv_id]}
        ... = 𝟙 X ≫ inv g:
        by {symmetry' at h1, rw [h1, category.assoc]}
        ... = inv g:
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

def left_right_inv_iso {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) (h : Y ⟶ X) [is_iso g] [is_iso h]: 
f ≫ g = 𝟙 X ∧ h ≫ f = 𝟙 Y → is_iso f :=
begin
    intro h1,
    cases h1 with hgx hhy,
    have hg : g = h :=
        -- not proud of this one
        by {apply left_right_inv_eq, split, exact hgx, exact hhy},
    rw hg at hgx,
    have h2 : f = inv h :=
        by {apply at_most_one_inv, exact hgx},
    rw h2,
    apply is_iso.inv_is_iso,
end

/-Exercise 1.1.ii-/
/-Let C be a category. Show that the collection of isomorphisms in C defines a 
subcategory, the maximal groupoid inside C.-/
--To do:
-- define objects (all obj of C)
-- define morphisms (just isomorphisms of C)
-- show that all morphisms have dom/cod? (spoiler: they do, we have all objects)
-- identity morphisms (again, they are isomorphisms)
-- closure of composite morphisms - probably the only hard part in Lean

def identity_is_iso (X : C) : is_iso (𝟙 X) :=
{ inv := 𝟙 X,
  hom_inv_id' := by rw [category.id_comp],
  inv_hom_id' := by rw [category.id_comp]}


-- need f.hom ≫ g.hom ≫ g.inv ≫ f.inv = 𝟙 X and vice versa
def iso_comp_is_iso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [is_iso f] [is_iso g] :
is_iso (f ≫ g) := 
{ inv := (inv g ≫ inv f),
  hom_inv_id' := by rw [← category.assoc, category.assoc f, is_iso.hom_inv_id, category.comp_id, is_iso.hom_inv_id],
  inv_hom_id' := by rw [← category.assoc, category.assoc (inv g), is_iso.inv_hom_id, category.comp_id, is_iso.inv_hom_id]}


def core (C : Type u) : Type u := C --objects are elements of type core C
variable (X : core C)
#check X --nice

-- don't think I need to show that it's a groupoid?

instance has_hom : core C :=
{ hom := is_iso }

instance core_groupoid : groupoid.{v} (core C) := { 
  hom := /-λ X Y : core C, X ⟶ Y-/sorry,
  id := by apply identity_is_iso,
  comp := _,
  id_comp' := _,
  comp_id' := _,
  assoc' := _,
  inv := _,
  inv_comp' := _,
  comp_inv' := _ } --hhhhh



/-Exercise 1.1.iii For any category C and any object A ∈ C, show that:-/

/-(i) There is a category A/C whose objects are morphisms f : A ⟶ X
with domain A and in which a morphism from f : A ⟶ X to g : A ⟶ Y
is a map h : X ⟶ Y such that g = hf.-/

/-instance unop_mono_of_epi {A B : Cᵒᵖ} (f : A ⟶ B) [epi f] : mono f.unop :=
⟨λ Z g h eq, has_hom.hom.op_inj ((cancel_epi f).1 (has_hom.hom.unop_inj eq))⟩-/


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

--ugh
/-class slice_struct (A : C) (obj : Type v) extends has_slice_hom.{v} obj : Type (max v (v+1)) :=
(id : Π {X : C}, (A ⟶ X) : obj, hom (A ⟶ X) (A ⟶ X). obviously)
(comp : Π {(A ⟶ X) (A ⟶ Y) (A ⟶ Z): AC}, (A ⟶ X) ⟶ (A ⟶ Y))-/


/-class slice (obj : Type u) extends category.{v} obj : Type (max u (v+1)) :=
(inv       : Π {X Y : obj}, (X ⟶ Y) → (Y ⟶ X))
(inv_comp' : ∀ {X Y : obj} (f : X ⟶ Y), comp (inv f) f = id Y . obviously)
(comp_inv' : ∀ {X Y : obj} (f : X ⟶ Y), comp f (inv f) = id X . obviously)-/