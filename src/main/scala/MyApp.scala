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
  def isValid(twelve: Twelve): Boolean = validations.forall(_.f(twelve))


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
    * @param to destination tuple
    */
  case class Movement(from: (Short, Vector[Short]), to: (Short, Vector[Short]))


  /** Returns list of movements by given Twelve, list of sources, and list of destinations
    *
    * @param twelve Twelve to shuffle
    * @param rowsFrom list of source rows
    * @param rowsTo list of destination rows
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
      val solutionsCurrent = twelves.filter(isValid)
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
        val movements = getMovements(twelve, validation.rows, rowsTo)
        val twlv = mutable.Map(twelve.toSeq: _*)
        movements.foreach { movement =>
          twlv += movement.from += movement.to
        }
        twlv.toMap
      }

      // the salt of fast method is to make this collection parallel
      val validTwelves = twelves.filter(validation.f).par
      val solutionsCurrent = twelves.filter(isValid)
      val solutionsNext = if (solutionsCurrent.nonEmpty) {
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

  val input = "5 7 4 4\n3 4 1 3\n7 1 5 4\n5 1 1 4\n4 2 4 2\n2 4 3 8\n5 1 1 4\n4 1 1 0\n1 0 7 5\n5 1 1 7\n4 2 4 2\n1 0 7 5"

  //val input = twelveToString(randomCubes()(new Random()))

  val startTime = new Date().getTime

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
    case _ =>
  }

  println(s"finished in ${(new Date().getTime - startTime) / 1000} s")

}
