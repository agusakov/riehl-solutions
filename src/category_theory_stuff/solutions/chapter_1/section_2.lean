import category_theory.category category_theory.epi_mono tactic-- this transitively imports

open category_theory

universes v u

variables (C : Type u) [category.{v} C]

/-Prove Lemma 1.2.11 by proving either (i) or (i') and either (ii) or (i'), 
then arguing by duality. Conclude that the monomorphisms in any category 
define a subcategory of that category and dually that the epimorphisms also 
define a subcategory. -/

/-Lemma 1.2.11(i) If f : x ⟶ y and g : y ⟶ z are monomorphisms, then so is 
gf : x ⟶ z.-/

lemma mono_comp_mono (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z) [hg : mono g] [hf : mono f]: 
mono (f ≫ g) :=
begin
    constructor, --what the heck this is so useful
    intros Z h k hcomp,
    repeat {rw ← category.assoc at hcomp},
    rw cancel_mono g at hcomp,
    rw cancel_mono f at hcomp,
    exact hcomp,
end

/-Lemma 1.2.11(ii) If f : x ⟶ y and g : y ⟶ z are morphisms so that gf is monic, 
then f is monic. -/

lemma comp_mono_mono (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z) [hfg : mono (f ≫ g)]: 
mono f :=
begin
    constructor,
    intros Z h k hf,
    rw ← cancel_mono (f ≫ g),
    repeat {rw ← category.assoc},
    rw hf,
end