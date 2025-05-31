# Semverif
A toy C static analyzer for a school project

## Domains

### Sign

The sign domain was quite easy to implement.

### Interval

The interval domain implementation is straightforward and we did not see any breaking 
point in it. One detail is that we wanted non relational abstract states to canonically
represent top elements (with a Top constructor), so we have to make sure that ]-inf; +inf[
is interpreted as a Top element in the implementation.

### Congruences

The congruences domain was a bit harder to implement than the sign domain or the interval
domain because of the meet operation.

### Boolean condition partitioning

We implemented the boolean condition partition mechanism as a kind of domain that serves
as a base for other domains. We had to extend the syntax of the langage we are working
with to handle boolean variables. We decided not to spend too much time on extending the
parser as the deadline approched and as it was not part of the core work of the domain.

### Reduced product of non-relational domains

The reduced product is quite straightforward too. We implemented it as a product (every
operation is just the product of them for each non relation domain). However, in order
to make it more precise, we pass computed results through a function that is meant to 
reduce an abstract state. 

#### Reduce function

We observed that both sign and congruences domain could refine interval domain. A given
sign can troncate an interval on zero. The refinement given by the congruence domain is
not this brutal : given a congruence abstract state aZ+b we shrink the size of the
interval to exclude borders that do not contain any number in the ring aZ+b.

```
{ [-9, 15], 4Z+0 } ----> { [-8, 12], 4Z+0 }
```

## Extensions

### Boolean condition partitioning

We decided to implement the boolean condition partitioning domain. It computes abstract
states linked with the set of current boolean variables of the program.

The key used to know what partition to work on is a list of the program's boolean
variables. During the whole analysis, the domain carries a key corresponding to the
current state of every program's boolean variables. 

The domain really acts in two situations :
    - Each time the domain computes a boolean assignment, an image of the current
      program's environment is saved and made accessible only through a given key (which
      is the current key with potentielly the new boolean variable in it).

    - Each time the domain computes a guard : if the guard expression is of the form b or
      !b with b a boolean variable, the current key is changed in order to focus the good
      partition in the domain

The key is represented as a list of boolean variables and the set of environments
partitions is represented as a hash table associating each key to one environment.

The main difference between this domain and other non relational domains is the presence
of three functions, that handle boolean assignments and guards.

```ocaml
val add_bool_cond : partitions -> string -> unit
val rm_bool_cond : partitions -> string -> unit
val split : partitions -> string -> bool_expr -> unit
```

The first two functions should be used when passing through the condition of a
conditional statement. For instance 

```c
if (b1) {           // <-- add_bool_cond st "b1"
    if (!b2) {      // <-- add_bool_cond st "b2"
        /* ... */    
    }               // <-- rm_bool_cond st "b2"
}                   // <-- rm_bool_cond st "b1"
```
     
This allows to keep track of the key to access the good partition.

The last function splits partitions. Splitting partitions occurs when a new boolean
variable is associated with a conditional expression. For instance

```c
bool b1 = x > 1;     // <-- split st "b1" <x > 1>
bool b2 = x == 1;    // <-- split st "b2" <x == 1>
```

In the first line, we create a partition in which the variable b1 is true and in which we
consider that x > 1. It works the same way for the second line.

Here is how the domain should theoritically work together with the interval domain :

```c
int x = rand(0, 100);    // parts :
                         //   - current key [] -> x in [0, 100]

bool b = x > 20;         // parts after 'split parts "b" <x > 0>' :
                         //   - current key [] -> x in [0, 100]
                         //   - [b] -> x in ]20, 100]

if (b) {                 // parts after 'add_bool_cond parts "b"'
                         //   - [] -> x in [0, 100]
                         //   - current key [b] -> x in ]20, 100]

    assert(x <= 20);     // guard checks the assertion in the partition given by the
                         // current key. So this assertion should fails.
}
```

The domain does not perfectly work as I wanted since I did not find any way to know when
I could remove a boolean condition from the current key after getting out from an if 
statement, inside the iterator.
