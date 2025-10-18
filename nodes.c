  #include "stdlib.h"

  struct node {
      struct node *next;
      int value;
  };

  /*@
  predicate nodes(struct node *node, int count) =
    node == 0 ?
      count == 0
    :
      0 < count
      &*& node->next |-> ?next &*& node->value |-> ?value
      &*& malloc_block_node(node) &*& nodes(next, count - 1);
  @*/

  struct node *make_nodes(int k)
      //@ requires k >= 0;
      //@ ensures nodes(result, k);
  {
    // write your solution here
  }