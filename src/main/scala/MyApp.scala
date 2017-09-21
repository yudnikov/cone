import java.util.Date
import java.util.Formatter.DateTime
import java.util.concurrent.ConcurrentHashMap

import scala.collection.mutable
import scala.concurrent.{Await, Future}
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration.Duration
import scala.util.Random

object MyApp extends App {

  /** FORMALISATION */

  /** Assume that single cube can be represented as Vector of Shorts in it's corners, counted from left to right:
    * 1 2
    * 3 4
    * because it's Vector, counting starts from 0
    */
  type Cube = Vector[Short]


  /** Assume that twelve cubes can be represented as map where key is cube's position in the figure, and the value is
    * the cube. We wouldn't define Twelve and Cube as classes because it needs to implement some methods when extending
    * Map or Vector. Let's use primitive data structures. Assume that row's counting starts from 1.
    */
  type Twelve = Map[Short, Cube]


  /** The validation condition can be represented as a list of functions. Each function takes some Twelve as argument
    * and returns true or false if twelve is valid or not. Than for convenience, define all rows which are referred in
    * current function as list.
    */
  case class Validation(f: Twelve => Boolean, rows: List[Short])


  /** Quest condition definition
    */
  val validations: List[Validation] = List(
    Validation(c => c(1)(3) + c(2)(2) + c(4)(1) + c(5)(0) == 10, List(1, 2, 4, 5)),
    Validation(c => c(3)(3) + c(4)(2) + c(7)(1) + c(8)(0) == 10, List(3, 4, 7, 8)),
    Validation(c => c(4)(3) + c(5)(2) + c(8)(1) + c(9)(0) == 10, List(4, 5, 8, 9)),
    Validation(c => c(5)(3) + c(6)(2) + c(9)(1) + c(10)(0) == 10, List(5, 6, 9, 10)),
    Validation(c => c(8)(3) + c(9)(2) + c(11)(1) + c(12)(0) == 10, List(8, 9, 11, 12)),
    Validation(c => c(1)(2) + c(3)(1) + c(4)(0) <= 10, List(1, 3, 4)),
    Validation(c => c(2)(3) + c(5)(1) + c(6)(0) <= 10, List(2, 5, 6)),
    Validation(c => c(7)(3) + c(8)(2) + c(11)(0) <= 10, List(7, 8, 11)),
    Validation(c => c(9)(3) + c(10)(2) + c(12)(1) <= 10, List(9, 10, 12)),
    Validation(c => c(1)(1) + c(2)(0) <= 10, List(1, 2)),
    Validation(c => c(3)(2) + c(7)(0) <= 10, List(3, 7)),
    Validation(c => c(6)(3) + c(10)(1) <= 10, List(6, 10)),
    Validation(c => c(11)(3) + c(12)(2) <= 10, List(11, 12))
  )


  /** Let's define a method to validate a Twelve.
    *
    * @param twelve some Twelve to validate
    * @return is valid or not
    */
  def isSolution(twelve: Twelve): Boolean = validations.forall(_.f(twelve))


  /** Let's define reverse index for validations, where the key is row number, and a value list of functions
    */
  val validationsRev: Map[Short, List[Twelve => Boolean]] = validations.flatMap { t =>
    t.rows.map { int =>
      int -> t.f
    }
  } groupBy (_._1) map { t =>
    t._1 -> t._2.map(_._2)
  }


  /** Converts Twelve to string, separated at first by " ", than by "\n"
    *
    * @param cube cube to serialize
    * @return result string
    */
  def twelveToString(cube: Twelve): String = cube.keys.toSeq.sorted.map(cube(_).mkString(" ")).mkString("\n")


  /** Extracts Twelve from string
    *
    * @param string to extract
    * @return maybe Twelve
    */
  def twelveFromString(string: String): Option[Twelve] = {

    val rows = string.trim.split("\n")

    // assume that rows.length eq 12
    if (rows.length != 12) {
      return None
    }

    var i = 0
    val vectors = rows.map { s =>
      i += 1
      i.toShort -> s.split(" ").map(_.toShort).toVector
    }
    Some(vectors.toMap)
  }


  /** Let's define method to get cartesian sum of N lists of X elements each. We'll need distinct.
    *
    * @param list list of list's
    * @tparam T type of the element
    * @return list of merged lists
    */
  def cartesianDistinct[T](list: List[List[T]]): List[List[T]] = {

    /** Simple cartesian sum
      *
      * @param list list of list's to add
      * @return list of merged list's
      */
    def cartesian(list: List[List[T]]): List[List[T]] = list match {
      case Nil =>
        List(Nil)
      case h :: t =>
        for (hh <- h; tt <- cartesian(t)) yield hh :: tt
    }

    cartesian(list).filter(list => list == list.distinct)
  }


  /** Defines Twelve's cells (rows) movement
    *
    * @param from source tuple
    * @param to   destination tuple
    */
  case class Movement(from: (Short, Vector[Short]), to: (Short, Vector[Short]))


  /** Returns list of movements by given Twelve, list of sources, and list of destinations
    *
    * @param twelve   Twelve to shuffle
    * @param rowsFrom list of source rows
    * @param rowsTo   list of destination rows
    * @return list of movements
    */
  def getMovements(twelve: Twelve, rowsFrom: List[Short], rowsTo: List[Short]): List[Movement] = {
    var i = 0
    rowsFrom.map { row =>
      val rowTo = rowsTo(i)
      i = i + 1
      val movement = if (row != rowTo) {
        val value = twelve(rowTo)
        val res = Movement(rowTo -> twelve(row), row -> value)
        Some(res)
      } else {
        None
      }
      movement
    }.filter(_.nonEmpty).map(_.get)
  }

  def getMovements2(twelve: Twelve, rowsFrom: List[Short], rowsTo: List[Short]): List[Movement] = {
    val d1 = rowsFrom.diff(rowsTo)
    val d2 = rowsTo.diff(rowsFrom)
    if (d1.length == d2.length) {
      val r1 = d2.zip(d1).map(t => Movement(t._1 -> twelve(t._2), t._2 -> twelve(t._1)))
      val r2 = d2.zip(d1.reverse).map(t => Movement(t._1 -> twelve(t._2), t._2 -> twelve(t._1)))
      val res = r1.union(r2).distinct
      res
    } else {
      Nil
    }
  }

  def getMovements3(twelve: Twelve, rowsFrom: List[Short], rowsTo: List[Short]): List[Movement] = ???

  // thread safe cache
  val cache: ConcurrentHashMap[List[List[Short]], List[List[Short]]] = new ConcurrentHashMap()


  def getVariants(rows: List[Short], rowsToShuffle: List[Short]): List[List[Short]] = {
    val key = List.fill(rows.length)(rowsToShuffle)
    cache.get(key) match {
      case null =>
        val value = cartesianDistinct(key).diff(List(rows))
        cache.put(key, value)
        value
      case value =>
        value
    }
  }


  /** Entry point for linear solution
    *
    * @param twelve0 start value
    * @return list of valid Twelves
    */
  def solve(twelve0: Twelve): List[Twelve] = {

    // Let's pre-calculate some important values

    // all possible rows
    val rows = twelve0.keys.toList.sorted


    def solve(twelve: Twelve, validations: List[Validation], rowsFixed: List[Short], solutions: List[Twelve]): List[Twelve] = {

      val validation = if (validations.nonEmpty)
        validations.head
      else
        return Nil

      val rowsToShuffle = rows.diff(rowsFixed)
      val variants = getVariants(validation.rows, rowsToShuffle)
      val twelves = variants.map { rowsTo =>
        val movements = getMovements(twelve, validation.rows, rowsTo)
        val twlv = mutable.Map(twelve.toSeq: _*)
        movements.foreach { movement =>
          twlv += movement.from += movement.to
        }
        twlv.toMap
      }

      val validTwelves = twelves.filter(validation.f)
      val solutionsCurrent = twelves.filter(isSolution)
      val solutionsNext = if (solutionsCurrent.nonEmpty) {
        solutionsCurrent.union(solutions).distinct
      } else {
        solutions
      }

      if (validTwelves.nonEmpty && solutionsCurrent.nonEmpty) {
        solutionsNext
      } else {
        validTwelves.flatMap { twlv =>
          solve(twlv, validations.tail, rowsFixed.union(validation.rows), solutionsNext)
        }
      }

    }

    solve(twelve0, validations, Nil, Nil)

  }


  /** Entry point for concurrent solution
    *
    * @param twelve0 start value
    * @return list of valid Twelves
    */
  def solveFuture(twelve0: Twelve): Future[List[Twelve]] = {

    val cubes0: List[Cube] = twelve0.values.toList

    def validate(twelve: Twelve): Boolean = twelve.values.toList.diff(cubes0) == Nil

    // all possible rows
    val rows = twelve0.keys.toList.sorted

    def solveFuture(twelve: Twelve, validations: List[Validation], rowsFixed: List[Short], solutions: List[Twelve]): Future[List[Twelve]] = {

      val validation = if (validations.nonEmpty)
        validations.head
      else
        return Future(Nil)

      val rowsToShuffle = rows.diff(rowsFixed)
      val variants = getVariants(validation.rows, rowsToShuffle)
      val twelves = variants.map { rowsTo =>
        val movements = getMovements2(twelve, validation.rows, rowsTo)
        val twlv = mutable.Map(twelve.toSeq: _*)
        movements.foreach { movement =>
          twlv += movement.from += movement.to
        }
        val res = twlv.toMap
        res
      }.distinct

      val twelves2 = variants.map { rowsTo =>
        val movements = getMovements(twelve, validation.rows, rowsTo)
        val twlv = mutable.Map(twelve.toSeq: _*)
        movements.foreach { movement =>
          twlv += movement.from += movement.to
        }
        val res = twlv.toMap
        res
      }.distinct.filter(validate)

      val v1 = twelves.filter(validate)
      val v2 = twelves2.filter(validate)
      val d1 = v1.distinct
      val d2 = v2.distinct

      val diff = d2.diff(d1)

      // the salt of fast method is to make this collection parallel
      val validTwelves = twelves2.filter(validation.f).par
      val solutionsCurrent = twelves2.filter(isSolution)
      val solutionsNext = if (solutionsCurrent.nonEmpty) {
        solutionsCurrent.foreach { t =>
          if (!validate(t))
            println(s"invalid \n$t")
        }
        solutionsCurrent.union(solutions).distinct
      } else {
        solutions
      }

      if (validTwelves.nonEmpty && solutionsCurrent.nonEmpty) {
        Future(solutionsNext)
      } else {
        val res = validTwelves.map { twlv =>
          solveFuture(twlv, validations.tail, rowsFixed.union(validation.rows), solutionsNext)
        }
        Future.sequence(res.toList).map(_.flatten)
      }
    }

    solveFuture(twelve0, validations, Nil, Nil)

  }

  def randomCubes(l: Int = 12, n: Int = 4)(implicit r: Random): Twelve = {
    val res = for (i <- 1 to l) yield i.toShort -> (for (_ <- 1 to n) yield r.nextInt(10).toShort).toVector
    res.toMap
  }

  val inputs = List(
    "9 1 6 4\n2 0 4 7\n5 2 5 7\n2 1 1 2\n1 2 2 6\n1 1 1 0\n5 1 9 2\n1 3 4 0\n3 2 5 3\n1 0 4 7\n4 3 1 1\n2 3 0 3",
    "5 1 9 2\n1 3 4 0\n3 2 5 3\n1 0 4 7\n4 3 1 1\n2 3 0 3\n9 1 6 4\n2 0 4 7\n5 2 5 7\n2 1 1 2\n1 2 2 6\n1 1 1 0",
    "4 3 1 1\n2 3 0 3\n9 1 6 4\n2 0 4 7\n5 2 5 7\n5 1 9 2\n1 3 4 0\n3 2 5 3\n1 0 4 7\n2 1 1 2\n1 2 2 6\n1 1 1 0"/*,
    "1 0 7 5\n3 4 1 3\n5 1 1 4\n7 6 1 8\n5 7 4 4\n8 3 3 4\n7 1 5 4\n4 1 1 0\n3 1 1 4\n2 4 3 8\n5 1 1 7\n4 2 4 2",
    "5 7 4 4\n3 4 1 3\n7 1 5 4\n5 1 1 4\n4 2 4 2\n2 4 3 8\n5 1 1 4\n4 1 1 0\n1 0 7 5\n5 1 1 7\n4 2 4 2\n1 0 7 5",
    "8 0 5 1\n4 4 3 6\n3 7 1 2\n5 0 5 2\n3 0 4 3\n5 1 0 7\n4 0 3 3\n5 4 6 0\n3 4 3 0\n1 7 3 8\n0 7 7 3\n3 2 0 4",
    "1 6 4 0\n6 1 3 5\n4 0 5 2\n4 1 3 5\n5 1 4 2\n6 5 5 4\n4 0 4 6\n5 2 1 4\n4 6 0 1\n2 0 1 4\n3 0 4 5\n4 0 5 1",
    "3 3 3 4\n4 1 3 5\n4 5 3 4\n5 2 1 3\n3 3 7 4\n2 1 3 3\n3 2 6 1\n4 3 3 4\n5 2 2 2\n4 2 2 3\n5 5 1 4\n1 2 5 3"*/
  )

  def solveInput(input: String): Unit =
    twelveFromString(input) match {
      case Some(twelve) =>
        val result = Await.result(solveFuture(twelve), Duration.Inf)
        result match {
          case Nil =>
            println(s"The quest has no solutions")
          case l: List[Twelve] =>
            println(s"The quest has ${l.length} solutions: \n\n${l.map(twelveToString).mkString("\n\n")}")
          case _ =>
            println("Something went wrong...")
        }
        cache.clear()
      case _ =>
    }

  inputs.foreach { input =>
    println("*" * 64)
    println(s"input = \n$input \nsolving...")
    val startTime = new Date().getTime
    solveInput(input)
    println(s"finished in ${(new Date().getTime - startTime) / 1000} s")
  }

}
