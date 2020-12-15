package org.hablapps.dotty.shapeaware

/*
THE PROBLEM
*/

object TheProblem {

  sealed abstract class Tree[A]
  case class Leaf[A](a : A) extends Tree[A]
  case class Node[A](left: Tree[A], root: A, right: Tree[A]) extends Tree[A]

  class FirstAttemptLeafs[A]{

    def get(tree: Tree[A]): List[A] = ???

    def update(tree: Tree[A]): List[A] => Tree[A] = ???
  }

  class Leafs[A]{

    def get(tree: Tree[A]): List[A] = tree match {
      case Leaf(root) => List(root)
      case Node(left, _, right) => get(left) ++ get(right)
    }

    def update(tree: Tree[A]): List[A] => Option[(List[A], Tree[A])] =
      ??? // tree match {
    //   case Leaf(_) => for {
    //     (head :: tail) <- StateT.get[Option, List[A]]
    //     _ <- StateT.set(tail)
    //   } yield Leaf(head)

    //   case Node(left, root, right) =>
    //     update(left).map2(update(right))(Node(_, root, _))
    // }
  }

  val leavesInt = new Leafs[Int]
  import leavesInt._

  // describe("test1"){
  //   val t: Tree[Int] = Node(Leaf(1), 2, Leaf(3))

  //   val c: StateT[Option, List[Int], Tree[Int]] = update(t)

  //   it("Ok"){
  //     c.runA(List(3, 4)) shouldBe Some(Node(Leaf(3), 2, Leaf(4)))
  //   }

  //   it("No Ok"){
  //     c.runA(List(3)) shouldBe None
  //   }

  //   it("Exceeds"){
  //     c.run(List(3,4,5)) shouldBe Some((List(5), Node(Leaf(3), 2, Leaf(4))))
  //   }
  // }
}

object TheSolutionInScala {

  sealed abstract class Tree[A]{
    type This <: Tree[A]{ type This = this.type }
    def leafs: LeafsShape[A, This]
  }

  case class Leaf[A](value: A) extends Tree[A]{
    type This = Leaf[A]
    def leafs: Cons[A, Nil[A]] = Cons(value, Nil())
  }

  case class Node[L <: Tree[A], A, R <: Tree[A]](left: L, root: A, right: R) extends Tree[A]{
    type This = Node[L, A, R]
    def leafs: Concat[A, LeafsShape[A, L], LeafsShape[A, R]] =
      ???// (left.leafs: LeafsShape[A, L]) concat (right.leafs: LeafsShape[A, R])
  }

  sealed abstract class List[A]{
    type This <: List[A]{ type This = this.type }
    def concat[L <: List[A]](l: L): Concat[A, This, L]
  }
  case class Nil[A]() extends List[A]{
    type This = Nil[A]
    def concat[L <: List[A]](l: L): L = l
  }
  case class Cons[A, T <: List[A]](head: A, tail: T) extends List[A]{
    type This = Cons[A, T]
    def concat[L <: List[A]](l: L): Cons[A, Concat[A, tail.This, L]] =
      Cons(head, tail concat l)
  }

  type Concat[A, L1 <: List[A], L2 <: List[A]] <: List[A] = L1 match {
    case Nil[A] => L2
    case Cons[A, t] => Cons[A, Concat[A, t, L2]]
  }

  type LeafsShape[A, In <: Tree[A]] <: List[A] = In match {
    case Leaf[A] => Cons[A, Nil[A]]
    case Node[l, A, r] => Concat[A, LeafsShape[A, l], LeafsShape[A, r]]
  }

  class Leafs[A]{

    def get[In <: Tree[A]](t : In): LeafsShape[A, In] = t match {
      case Leaf(a): Leaf[A] => ??? // Cons[A, Nil[A]](a, Nil[A]()) // .asInstanceOf[LeafsShape[A, In]]
      case Node(l, a, r) => ???
    }

    def update[In <: Tree[A]](t : In): LeafsShape[A, In] => In = ???
  }

//   val leavesInt = new Leafs[Int]

//   describe("Ok"){

//     it("one focus"){
//       val t = Leaf(1)

//       leavesInt.get(t) shouldBe
//         Cons(1, Nil[Int]())

//       leavesInt.update(t).apply(Cons(3, Nil[Int]())) shouldBe
//         Leaf(3)
//     }

//     it("two foci"){
//       val t = Node(Node(Leaf(1), 2, Leaf(3)), 4, Leaf(5))

//       leavesInt.get(t) shouldBe
//         Cons(1, Cons(3, Cons(5, Nil[Int]())))

//       leavesInt.update(t).apply(Cons(5, Cons(3, Cons(1, Nil[Int]())))) shouldBe
//         Node(Node(Leaf(5), 2, Leaf(3)), 4, Leaf(1))
//     }
//   }

//   describe("No OK"){

//     val t = Node(Node(Leaf(1), 2, Leaf(3)), 4, Leaf(5))

//     it("Not enough values"){
//       """
//         leavesInt.update(t).apply(Cons(1, Cons(2, Nil[Int]())))
//       """ shouldNot compile
//     }

//     it("Exceeds values"){
//       """
//         leavesInt.update(t).apply(Cons(5, Cons(4, Cons(3, Cons(2, Nil[Int]())))))
//       """ shouldNot compile
//     }
//   }
}

// object TheSolutionInScalaWithNat extends TheSolutionInScalaWithNat
// class TheSolutionInScalaWithNat extends FunSpec with Matchers{

//   sealed abstract class Tree[A]
//   case class Leaf[A](value: A) extends Tree[A]
//   case class Node[L <: Tree[A], A, R <: Tree[A]](left: L, root: A, right: R) extends Tree[A]

//   import shapeless.{Sized, Nat}

//   class Leafs[A]{

//     def get[T <: Tree[A]](t : T)(implicit E: LeafsShape[T]) = E.get(t)

//     def put[T <: Tree[A]](t : T)(implicit E: LeafsShape[T]) = E.put(t)

//     trait LeafsShape[T <: Tree[A]]{
//       type N <: Nat

//       def get(t: T): Sized[List[A], N]
//       def put(t: T): Sized[List[A], N] => T
//     }

//     object LeafsShape{
//       import shapeless.{Succ, _0}
//       import shapeless.syntax.sized._

//       implicit def leafCase = new LeafsShape[Leaf[A]]{
//         type N = Succ[_0]

//         def get(t: Leaf[A]) =
//           Sized[List](t.value)

//         def put(t: Leaf[A]) = {
//           case Sized(value) => Leaf(value)
//         }
//       }

//       import shapeless.ops.nat.{ToInt, Diff, Sum}

//       implicit def nodeCase[
//           L <: Tree[A], NL <: Nat,
//           R <: Tree[A], NR <: Nat,
//           M <: Nat](implicit
//           LeafsShapeL: LeafsShape[L]{ type N = NL },
//           LeafsShapeR: LeafsShape[R]{ type N = NR },
//           S: Sum.Aux[NL, NR, M],
//           D: Diff.Aux[M, NL, NR],
//           TI: ToInt[NL]) = new LeafsShape[Node[L, A, R]]{
//         type N = M

//         def get(t: Node[L, A, R]) =
//           LeafsShapeL.get(t.left) ++ LeafsShapeR.get(t.right)

//         def put(t: Node[L, A, R]) = _.splitAt[NL] match {
//           case (il, ir) =>
//             Node(LeafsShapeL.put(t.left)(il), t.root, LeafsShapeR.put(t.right)(ir))
//         }
//       }
//     }
//   }

//   val leavesInt = new Leafs[Int]

//   describe("Ok"){

//     it("one focus"){
//       val t = Leaf(1)

//       leavesInt.get(t) shouldBe
//         Sized(1)

//       leavesInt.put(t).apply(Sized[List](3)) shouldBe
//         Leaf(3)
//     }

//     it("two foci"){
//       val t = Node(Node(Leaf(1), 2, Leaf(3)), 4, Leaf(5))

//       leavesInt.get(t) shouldBe
//         Sized(1, 3, 5)

//       leavesInt.put(t).apply(Sized[List](5, 3, 1)) shouldBe
//         Node(Node(Leaf(5), 2, Leaf(3)), 4, Leaf(1))
//     }
//   }

//   describe("No OK"){

//     val t = Node(Node(Leaf(1), 2, Leaf(3)), 4, Leaf(5))

//     it("Not enough values"){
//       """
//         leavesInt.put(t).apply(Sized[List](1, 2))
//       """ shouldNot compile
//     }

//     it("Exceeds values"){
//       """
//         leavesInt.put(t).apply(Sized[List](1, 2, 3, 4))
//       """ shouldNot compile
//     }
//   }

// }

