# Semverif
A toy C static analyzer for a school project

# Extensions

## Boolean condition partitioning

We implemented the boolean condition partition mechanism as a kind of domain that serves
as a base for other domains. We had to extend the syntax of the langage we are working
with to handle boolean variables. We decided not to spend too much time on extending the
parser as the deadline approched and as it was not part of the core work of the domain.

### Implementation

#### How the domain works

The key used to know what partition to work on is a list of the program's boolean
variables associated with their value. During the whole analysis, the domain carries a
key corresponding to the current state of every program's boolean variables. 

Each time the domain computes a boolean assignment
  - the key is changed to reflect the current program's state
  - an image of the current program's environment is saved and made accessible only
    through the freshly updated key

Similarly, each time the domain computes a guard

#### Implementation details

The key is represented as a list of boolean variables and the set of environments
partitions is represented as a hash table associating each key to one environment.
The domain is underlying other domains and the latters do not know the existence of it,
as it makes the current used environment available for them and as they cannot interface
with it.
