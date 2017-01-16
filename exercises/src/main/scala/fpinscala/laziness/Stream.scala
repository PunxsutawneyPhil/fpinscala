package fpinscala.laziness

import Stream._
trait Stream[+A] {

  def toList: List[A] =
    this match {
      case Empty => Nil
      case Cons(h, t) => h() :: t().toList
    }

  def foldRight[B](z: => B)(f: (A, => B) => B): B = // The arrow `=>` in front of the argument type `B` means that the function `f` takes its second argument by name and may choose not to evaluate it.
  {
    this match {
      case Cons(h, t) => f(h(), t().foldRight(z)(f)) // If `f` doesn't evaluate its second argument, the recursion never occurs.
      case _ => z
    }
  }

  def scanRight[B](z: B)(f: (A, => B) => B): Stream[B] =
    foldRight((z, Stream(z)))((a, p0) => {
      // p0 is passed by-name and used in by-name args in f and cons. So use lazy val to ensure only one evaluation...
      lazy val p1 = p0
      val b2 = f(a, p1._1)
      (b2, cons(b2, p1._2))
    })._2

  def exists(p: A => Boolean): Boolean = 
    foldRight(false)((a, b) => p(a) || b) // Here `b` is the unevaluated recursive step that folds the tail of the stream. If `p(a)` returns `true`, `b` will never be evaluated and the computation terminates early.

  @annotation.tailrec
  final def find(f: A => Boolean): Option[A] = this match {
    case Empty => None
    case Cons(h, t) => if (f(h())) Some(h()) else t().find(f)
  }
  def take(n: Int): Stream[A] =
    if (n <= 0) Empty
    else
      this match {
        case Empty => Empty
        case Cons(h, t) => cons(h(), t().take(n - 1))
      }

  def takeViaUnfold(n: Int): Stream[A] =
//    unfold((n, this)){
//      case (0, _) | (_, Empty) => None
//      case (n, Cons(h, t)) => Option(h(), (n-1, t()))
    unfold((this,n)) {
      case (Cons(h,t), 1) => Some((h(), (empty, 0)))
      case (Cons(h,t), n) if n > 1 => Some((h(), (t(), n-1)))
      case _ => None
    }

  def drop(n: Int): Stream[A] =
    if (n <= 0) this
    else
      this match {
        case Empty => Empty
        case Cons(h, t) => t().drop(n - 1)
      }

  def takeWhilePatternMatch(p: A => Boolean): Stream[A] =
    this match {
      case Cons(h, t) if p(h()) => cons(h(), t().takeWhile(p))
      case _ => empty
    }

  def takeWhile(p: A => Boolean): Stream[A] =
    foldRight(empty[A])((h,t) =>
      if (p(h)) cons(h,t)
      else      empty)

  def takeWhileViaUnfold(p: A => Boolean): Stream[A] =
    unfold(this){
      case Cons(h, t) if p(h()) => Option(h(), t())
      case _ => None
    }

  def forAll(p: A => Boolean): Boolean =
    foldRight(true)((a, b) => p(a) && b)

  def headOption: Option[A] =
    foldRight(None: Option[A])((h, t) => Some(h))

  // 5.7 map, filter, append, flatmap using foldRight. Part of the exercise is
  // writing your own function signatures.

  def map[B](f: A => B): Stream[B] =
    foldRight(empty[B])((h, t) => cons(f(h), t))

  def mapViaUnfold[B](f: A => B): Stream[B] =
    unfold(this){
      case Empty => None
      case Cons(h, t) => Option((f(h()), t()))
    }

  def zipWith[B,C](b: Stream[B])(f: (A,B) => C): Stream[C] =
    unfold((this, b)){
      case (Cons(h1,t1), Cons(h2,t2)) => Option(f(h1(), h2()),(t1(), t2()))
      case _ => None
    }

  def zipAll[B](s2: Stream[B]): Stream[(Option[A], Option[B])] =
    unfold((this, s2)){
      case (Cons(h1,t1), Cons(h2,t2)) => Option((Option(h1()), Option(h2())), (t1(), t2()))
      case (Cons(h1,t1), _) => Option((Option(h1()), None), (t1(), empty))
      case (_, Cons(h2,t2)) => Option((None, Option(h2())), (empty, t2()))
      case _ => None
    }

  def filter(f: A => Boolean): Stream[A] =
    foldRight(empty[A])((h, t) => if (f(h)) cons(h, t) else t )

  def append[B >: A](s: => Stream[B]): Stream[B] =
    foldRight(s)((h, t) => cons(h, t))

  def flatMap[B](f: A => Stream[B]): Stream[B] =
    foldRight(empty[B])((h, t) => f(h).append(t))

  def startsWith[B](s: Stream[B]): Boolean =
    zipAll(s).takeWhile(!_._2.isEmpty) forAll {
      case (h,h2) => h == h2
    }

  def tails: Stream[Stream[A]] =
    cons(this, unfold(this){
      case Cons(h,t) => Option(t(), t())
      case Empty => None
    })

  def hasSubsequence[B >: A](sub: Stream[B]): Boolean =
    tails.exists(_.startsWith(sub))
}
case object Empty extends Stream[Nothing]
case class Cons[+A](h: () => A, t: () => Stream[A]) extends Stream[A]

object Stream {
  def cons[A](hd: => A, tl: => Stream[A]): Stream[A] = {
    lazy val head = hd
    lazy val tail = tl
    Cons(() => head, () => tail)
  }

  def empty[A]: Stream[A] = Empty

  def apply[A](as: A*): Stream[A] =
    if (as.isEmpty) empty 
    else cons(as.head, apply(as.tail: _*))

  val onesOrig: Stream[Int] = Stream.cons(1, onesOrig)

  val ones: Stream[Int] = unfold(1)(_ => Option(1, 1))

  def constantOrig[A](a: A): Stream[A] = {
    lazy val tail: Stream[A] = Cons(() => a, () => tail)
    tail
  }

  def constant[A](a: A): Stream[A] =
    unfold(a)(_ => Option(a, a))


  def fromOrig(n: Int): Stream[Int] = {
    cons(n, fromOrig(n+1))
  }

  def from(n: Int): Stream[Int] =
    unfold(n)(s => Option(s, s+1))

  def fibsOrig(): Stream[Int] = {
    def fibLoop(n1: Int, n2: Int): Stream[Int] = {
      cons(n1, fibLoop(n2, n1 + n2))
    }
    fibLoop(0, 1)
  }

  def fibs(): Stream[Int] =
    unfold((0, 1)){case (s1, s2)  => Option(s1, (s2, s1 + s2))}

  def unfold[A, S](z: S)(f: S => Option[(A, S)]): Stream[A] = {
    f(z) match {
      case None => empty[A]
      case Some((next, s)) => cons(next, unfold(s)(f))
    }
  }

  def fibs2(z: (Int, Int))(f: ((Int, Int)) => Option[(Int, (Int, Int))]): Stream[Int] = {
//    f(z).foldRight(empty[Int])(p: (Int, (Int, Int)) => cons(p._1, fibs2(p._2)(f)))
    f(z) match {
      case None => empty[Int]
      case Some((next, s)) => cons(next, fibs2(s)(f))
    }
    //Stream.fibs2((0,1))(s => Option(s._1 + s._2, (s._2, s._1 + s._2))).take(12).toList
  }
}