# Stato del Progetto — Allegorie e Term Relation Algebras in Lean 4

## Obiettivo della tesi
Formalizzare meccanicamente in Lean 4 la teoria delle allegorie e delle Term Relation 
Algebras (TRA) seguendo:
- Ferro, *Towards a Relational Theory of Meaning: Allegorical Foundations*, 
  Università di Padova, 2024/2025
- Gavazzo, *Allegories of Symbolic Manipulations*, LICS 2023
- Freyd-Scedrov, *Categories, Allegories*, 1990

Contributo: prima formalizzazione meccanizzata di questa teoria in Lean 4 (non esiste 
in Mathlib). Documentare l'uso di LLM nel processo di formalizzazione.

Supervisore: Prof. Francesco Gavazzo, Università di Padova.
Colloquio: giovedì.

## Setup tecnico
- Lean 4 con Mathlib, progetto locale con lakefile.lean
- VS Code + estensione Lean 4
- Claude Code come agente interattivo
- Arch Linux

## Struttura del progetto
```
allegories/
├── lakefile.lean
├── Allegories.lean          ← file indice
└── Allegories/
    ├── Basic.lean           ← COMPLETO, zero sorry
    ├── Lemmas.lean          ← COMPLETO, zero sorry
    ├── Structures.lean      ← COMPLETO, zero sorry
    ├── Relator.lean         ← COMPLETO, zero sorry
    ├── RelationAlgebra.lean ← IN CORSO, sorry nei lemmi
    └── TRA.lean             ← DA FARE
```

## Convenzioni di stile
- Nomi inglesi, snake_case, nomi lunghi descrittivi
- @[simp] solo fuori dalla classe, solo su regole terminanti
- intersection_commutativity deliberatamente NON @[simp] (loop infinito)
- Dimostrazioni sempre esterne alla classe
- docstring /-- ... -/ su ogni campo e teorema
- /-! ... -/ in cima a ogni file con Main definitions e References

## File completati

### Allegories/Basic.lean
```lean
class Allegory (A : Type*) extends Category A where
  converse : ∀ {X Y : A}, (X ⟶ Y) → (Y ⟶ X)
  intersection : ∀ {X Y : A}, (X ⟶ Y) → (X ⟶ Y) → (X ⟶ Y)
  converse_id : ∀ {X : A}, converse (𝟙 X) = 𝟙 X
  converse_involution : ∀ {X Y : A} (R : X ⟶ Y), converse (converse R) = R
  intersection_idempotence : ∀ {X Y : A} (R : X ⟶ Y), intersection R R = R
  intersection_commutativity : ∀ {X Y : A} (R S : X ⟶ Y), intersection R S = intersection S R
  intersection_associativity : ∀ {X Y : A} (R S T : X ⟶ Y), 
      intersection R (intersection S T) = intersection (intersection R S) T
  converse_composition : ∀ {X Y Z : A} (R : X ⟶ Y) (S : Y ⟶ Z), 
      converse (R ≫ S) = converse S ≫ converse R
  converse_intersection : ∀ {X Y : A} (R S : X ⟶ Y), 
      converse (intersection R S) = intersection (converse R) (converse S)
  composition_distributivity : ∀ {X Y Z : A} (R : X ⟶ Y) (S T : Y ⟶ Z), 
      R ≫ intersection S T = 
      intersection (intersection (R ≫ S) (R ≫ intersection S T)) (R ≫ T)
  modular_law : ∀ {X Y Z : A} (R : X ⟶ Y) (S : Y ⟶ Z) (T : X ⟶ Z), 
      intersection (R ≫ S) T = 
      intersection (intersection (R ≫ S) T) (intersection R (T ≫ converse S) ≫ S)
```
Assiomi @[simp] nel namespace Allegory: converse_id, converse_involution,
intersection_idempotence, intersection_associativity, converse_composition,
converse_intersection.

### Allegories/Lemmas.lean
```lean
def hom_le (R S : X ⟶ Y) : Prop := intersection R S = R
scoped[Allegory] notation:50 R:51 " ≤ₐ " S:51 => Allegory.hom_le R S
```
Teoremi dimostrati (tutti senza sorry):
- hom_le_reflexivity : R ≤ₐ R  
  proof: exact intersection_idempotence R
- hom_le_transitivity : R ≤ₐ S → S ≤ₐ T → R ≤ₐ T  
  proof: rw [← h1, ← intersection_associativity, h2, h1]
- hom_le_antisymmetry : R ≤ₐ S → S ≤ₐ R → R = S  
  proof: rw [← h1, intersection_commutativity, h2]
- converse_monotone : R ≤ₐ S → converse R ≤ₐ converse S  
  proof: rw [← converse_intersection]; rw [h]
- galois_law : R ≤ₐ converse S ↔ converse R ≤ₐ S  
  proof: constructor; intro h; simpa using converse_monotone h; 
         intro h; simpa using converse_monotone h
- intersection_le_left : intersection R S ≤ₐ R  
  proof: rw [← intersection_commutativity, intersection_associativity, 
             intersection_idempotence]
- intersection_le_right : intersection R S ≤ₐ S  
  proof: rw [← intersection_associativity, intersection_idempotence]
- le_intersection : R ≤ₐ S → R ≤ₐ T → R ≤ₐ intersection S T  
  proof: rw [intersection_associativity, h1, h2]

### Allegories/Structures.lean
```lean
class TabularAllegory (A : Type*) extends Allegory A where
  protected has_tabulation : ∀ {X Y : A} (R : X ⟶ Y),
    ∃ (E : A) (h : E ⟶ X) (k : E ⟶ Y),
      R = converse h ≫ k ∧
      intersection (h ≫ converse h) (k ≫ converse k) = 𝟙 E

class UnitaryAllegory (A : Type*) extends Allegory A where
  unit_object : A
  protected unit_top : ∀ (R : unit_object ⟶ unit_object), R ≤ₐ 𝟙 unit_object
  protected unit_total : ∀ (B : A), ∃ (S : B ⟶ unit_object), 𝟙 B ≤ₐ S ≫ converse S

class LocallyCompleteAllegory (A : Type*) extends Allegory A where
  homCompleteLattice : ∀ X Y : A, CompleteLattice (X ⟶ Y)

@[reducible]
instance instHomCompleteLattice {A : Type*} [LocallyCompleteAllegory A] (X Y : A) :
    CompleteLattice (X ⟶ Y) :=
  LocallyCompleteAllegory.homCompleteLattice X Y
```
Nota: Proposizione 3.1.2 (Rel(Map(A)) ≅ A) lasciata come TODO commento —
richiede Map(A) e Rel(-) non ancora definiti.

### Allegories/Relator.lean
```lean
namespace Allegory
structure Relator (A B : Type*) [Allegory A] [Allegory B] extends A ⥤ B where
  protected map_converse : ∀ {X Y : A} (R : X ⟶ Y),
      toFunctor.map (converse R) = converse (toFunctor.map R)
  protected map_monotone : ∀ {X Y : A} {R S : X ⟶ Y},
      R ≤ₐ S → toFunctor.map R ≤ₐ toFunctor.map S

namespace Relator
def id (A : Type*) [Allegory A] : Relator A A where
  toFunctor    := 𝟭 A
  map_converse R := by simp
  map_monotone h := by simp; exact h

def comp (F : Relator A B) (G : Relator B C) : Relator A C where
  toFunctor    := F.toFunctor ⋙ G.toFunctor
  map_converse R := by simp; rw [F.map_converse, G.map_converse]
  map_monotone h := G.map_monotone (F.map_monotone h)

theorem map_hom_le (F : Relator A B) {X Y : A} {R S : X ⟶ Y} (h : R ≤ₐ S) :
    F.map R ≤ₐ F.map S := F.map_monotone h
```
Nota: map_intersection NON è un assioma — Ferro Def 3.2.1 ha solo 4 condizioni.
Solo una direzione è dimostrabile dalla monotonia (lemma map_intersection_le).

## File in corso

### Allegories/RelationAlgebra.lean
Struttura corretta, tutti i campi presenti, sorry solo nei lemmi del namespace.

Campi della classe (tutti assiomi, zero sorry):
- comp, identity, converse, left_residual, right_residual, star
- comp_assoc, identity_comp, comp_identity
- comp_sup_right, comp_sup_left, comp_bot, bot_comp
- converse_involution, galois_law
- left_residual_adjunction, right_residual_adjunction
- star_unfold, star_induction_left

Notazioni: ⊙ per comp, ° per converse, ⊸ per left_residual, ⊷ per right_residual, 
⋆ per star, tutte scoped[RelationAlgebra].

Lemmi con sorry da dimostrare:
1. converse_identity : converse (identity : A) = identity
   Strategia: le_antisymm + galois_law con a=identity, b=identity
   
2. converse_comp : converse (comp a b) = comp (converse b) (converse a)
   Strategia: le_antisymm + galois_law + residuals

3. converse_sup : converse (a ⊔ b) = converse a ⊔ converse b
   Strategia: le_antisymm + galois_law

4. comp_mono_left : a ≤ b → comp a c ≤ comp b c
   Strategia: comp_sup_left + join

5. comp_mono_right : b ≤ c → comp a b ≤ comp a c
   Strategia: comp_sup_right + join

6. identity_le_star : identity ≤ star a
   Strategia: rw [← star_unfold]; exact le_sup_left
   QUASI RISOLTA — prova: have h := star_unfold a; rw [← h]; exact le_sup_left

7. star_identity : star identity = identity
   Strategia: le_antisymm + star_induction_left + identity_comp

8. star_comp_star_le : comp (star a) (star a) ≤ star a
   Strategia: star_induction_left

## Da fare

### Allegories/TRA.lean — Ferro Definizione 4.3.1
Term Relation Algebra estende RelationAlgebra con:
- compatible_refinement (comp̃): a ≤ b → ã ≤ b̃, ∆̃ = ∆, ã;b̃ = (a;b)~, 
  ã° = (a°)~, ã* = (a*)~, struttura_induction: comp̃(R) ≤ R → ∆ ≤ R
- howe_extension (init): init(R) = comp̃(init(R));R, 
  init(S);R ≤ S → init(R) ≤ S

### Teoremi fondamentali da formalizzare
- Teorema 4.5.3 (α-TRA Soundness): LocallyCompleteAllegory + Relator + 
  algebra iniziale → A(A,A) è un α-TRA con comp e init
- Teorema 4.5.5 (Rappresentazione): ogni α-TRA ≅ A_A(X,X) per allegoria, 
  relatore e algebra iniziale opportuni

### Istanza lambda calcolo (contributo originale)
- Definire termini lambda come tipo induttivo
- Definire beta riduzione come relazione
- Dimostrare che istanzia la TRA
- Ottenere confluenza come corollario

## Decisioni di design già prese
- hom_le derivato da intersection (non assioma): intersection R S = R
- map_intersection NON assioma del Relator (non dimostrabile da sola monotonia)
- Proposizione 3.1.2 come TODO (richiede Map(A) e Rel(-))
- comp_bot e bot_comp come assiomi espliciti (ridondanti ma comodi)
- RelationAlgebra standalone — non dipende da Allegory
- Il collegamento Allegory ↔ RelationAlgebra viene in TRA.lean

## Lemmi Mathlib utili già usati
- le_sup_left : a ≤ a ⊔ b
- le_sup_right : b ≤ a ⊔ b  
- le_antisymm : a ≤ b → b ≤ a → a = b
- le_refl : a ≤ a
- Functor.id_map : (𝟭 C).map f = f  [@simp]
- Functor.comp_map : (F ⋙ G).map f = G.map (F.map f)  [@simp]
