import Math.Relation.RelIso
import Math.Order.Preorder

variable {α β: Type*} [LE α] [LT α] [LE β] [LT β]

def OrderEmbedding (α β: Type*) [LE α] [LE β] :=
  @RelEmbedding α β (· ≤ ·) (· ≤ ·)

def OrderIso (α β: Type*) [LE α] [LE β] :=
  @RelIso α β (· ≤ ·) (· ≤ ·)

infixl:25 " ↪o " => OrderEmbedding
infixl:25 " ≃o " => OrderIso
