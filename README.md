## CS550 - Persistent AVL Tree

The repository contains the course project for CS550 at EPFL.

- The implementation in `/src/main/scala/AVLTree.scala` can be verified with

```
[  Info  ] Stainless verification tool (https://github.com/epfl-lara/stainless)
[  Info  ] Version: 0.9.6
[  Info  ] Built at: 2022-07-03 15:30:00.685+0200
[  Info  ] Stainless Scala version: 3.0.2
[  Info  ] Bundled Scala compiler: 3.0.2
```

**The timeout should be set to larger than 5 for the verification.** 

In the branch `another-approach`, you can find another implementation that is also verified with Stainless.

An ideal extension of the current persistent AVL tree would look like `/src/main/scala/PersistentMockup.scala`, but unfortunately Stainless cannot verify all the nodes in the array `roots` are valid AVL trees, while a similar mockup `/src/main/scala/PersistentMockup.dfy` can be verified with Dafny.

- The implementation of the fat node method in Python can be found in `/src/fatnode/prototype.py`.

- `/src/dafny/BST-invalid.dfy` and `/src/dafny/BST.dfy` serve as an example of the difficulties we encountered while trying to verify the fat node implementation with Dafny, but it is itself not a fat node implementation in Dafny. `/src/dafny/BST.dfy` is just a copy from [Dafny's repo](https://github.com/dafny-lang/dafny/blob/master/Test/dafny4/BinarySearch.dfy). `/src/dafny/BST-invalid.dfy` has a different implementation of `InsertHelper`, but all other code is the same as in `/src/dafny/BST.dfy`.