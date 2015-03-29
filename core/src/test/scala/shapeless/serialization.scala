/*
 * Copyright (c) 2015 Miles Sabin
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package shapeless

import java.io._

import org.junit.Test
import org.junit.Assert._

import nat._
import ops.hlist._
import ops.function._
import poly.{ ~>> }
import syntax.{ CoproductOps, HListOps, RecordOps }
import syntax.singleton._
import test._

object SerializationTestDefns {
  def serializable[M](m: M): Boolean = {
    val baos = new ByteArrayOutputStream()
    val oos = new ObjectOutputStream(baos)
    var ois: ObjectInputStream = null
    try {
      oos.writeObject(m)
      oos.close()
      val bais = new ByteArrayInputStream(baos.toByteArray())
      ois = new ObjectInputStream(bais)
      val m2 = ois.readObject() // just ensure we can read it back
      ois.close()
      true
    } catch {
      case thr: Throwable =>
        thr.printStackTrace
        false
    } finally {
      oos.close()
      if (ois != null) ois.close()
    }
  }

  def assertSerializable[T](t: T) = assertTrue(serializable(t))

  object isDefined extends (Option ~>> Boolean) {
    def apply[T](o : Option[T]) = o.isDefined
  }

  object combineL extends Poly2 {
    implicit def ci = at[Int, Int]((acc, i) => acc+i)
    implicit def cs = at[Int, String]((acc, s) => acc+s.length)
    implicit def cb = at[Int, Boolean]((acc, b) => acc+(if(b) 1 else 0))
  }

  object combineR extends Poly2 {
    implicit def ci = at[Int, Int]((i, acc) => acc+i)
    implicit def cs = at[String, Int]((s, acc) => acc+s.length)
    implicit def cb = at[Boolean, Int]((b, acc) => acc+(if(b) 1 else 0))
  }

  object selInt extends Poly1 {
    implicit def ci = at[Int] { x => x }
  }

  object smear extends Poly {
    implicit val caseIntInt    = use((x: Int, y: Int) => x + y)
    implicit val caseStringInt = use((x: String, y: Int) => x.toInt + y)
    implicit val caseIntString = use((x: Int, y: String) => x + y.toInt)
  }

  trait Quux
  class Foo extends Quux
  class Bar extends Quux
  class Baz extends Quux
}

class SerializationTests {
  import SerializationTestDefns._

  @Test
  def testStructures {
    val l = 23 :: "foo" :: true :: HNil

    type ISB = Int :+: String :+: Boolean :+: CNil
    val ci = Coproduct[ISB](23)
    val cs = Coproduct[ISB]("foo")
    val cb = Coproduct[ISB](true)

    val r = 'foo ->> 23 :: 'bar ->> "foo" :: 'baz ->> true :: HNil

    assertTrue(serializable(HNil))
    assertTrue(serializable(l))

    assertTrue(serializable(ci))
    assertTrue(serializable(cs))
    assertTrue(serializable(cb))

    assertTrue(serializable(r))
  }

  @Test
  def testSyntax {
    val l = 23 :: "foo" :: true :: HNil

    type ISB = Int :+: String :+: Boolean :+: CNil
    val cs = Coproduct[ISB]("foo")

    val r = 'foo ->> 23 :: 'bar ->> "foo" :: 'baz ->> true :: HNil

    assertTrue(serializable(new HListOps(l)))

    assertTrue(serializable(new CoproductOps(cs)))

    assertTrue(serializable(new RecordOps(r)))
  }

  @Test
  def testHListOps {
    type L = Int :: String :: Boolean :: HNil
    type LP = String :: Boolean :: Int :: HNil
    type R = Boolean :: String :: Int :: HNil
    type LL = List[Int] :: List[String] :: List[Boolean] :: HNil
    type SL = Set[Int] :: Set[String] :: Set[Boolean] :: HNil
    type OL = Option[Int] :: Option[String] :: Option[Boolean] :: HNil
    type FL = (Int :: HNil) :: (String :: HNil) :: (Boolean :: HNil) :: HNil
    type Q = Foo :: Bar :: Baz :: HNil
    type IS = Int :: String :: HNil
    type LT = (Int, String) :: (Boolean, Double) :: (Char, Float) :: HNil
    type AL = (Int => Double) :: (String => Char) :: (Boolean => Float) :: HNil
    type I3 = Int :: Int :: Int :: HNil
    type K = HList.`'a, 'b, 'c`.T

    assertSerializable(IsHCons[L])

    assertSerializable(Mapped[L, List])

    assertSerializable(Comapped[LL, List])

    assertSerializable(NatTRel[LL, List, SL, Set])

    assertSerializable(HKernel[HNil])
    assertSerializable(HKernel[L])

    assertSerializable(ToCoproduct[HNil])
    assertSerializable(ToCoproduct[L])

    assertSerializable(Length[HNil])
    assertSerializable(Length[L])

    assertSerializable(Mapper[poly.identity.type, HNil])
    assertSerializable(Mapper[poly.identity.type, L])

    assertSerializable(FlatMapper[poly.identity.type, HNil])
    assertSerializable(FlatMapper[poly.identity.type, FL])

    assertSerializable(ConstMapper[Int, HNil])
    assertSerializable(ConstMapper[Int, L])

    assertSerializable(MapFolder[HNil, Boolean, isDefined.type])
    assertSerializable(MapFolder[OL, Boolean, isDefined.type])

    assertSerializable(LeftFolder[HNil, Int, combineL.type])
    assertSerializable(LeftFolder[L, Int, combineL.type])

    assertSerializable(RightFolder[HNil, Int, combineR.type])
    assertSerializable(RightFolder[L, Int, combineR.type])

    assertSerializable(LeftReducer[L, combineL.type])

    assertSerializable(RightReducer[R, combineR.type])

    assertSerializable(Unifier[HNil])
    assertSerializable(Unifier[Q])

    assertSerializable(SubtypeUnifier[HNil, Quux])
    assertSerializable(SubtypeUnifier[Q, Quux])

    // Depends on CanBuildFrom
    //assertSerializable(ToTraversable[HNil, List])
    //assertSerializable(ToTraversable[L, List])

    // Depends on CanBuildFrom
    //assertSerializable(ToSized[HNil, List])
    //assertSerializable(ToSized[L, List])

    assertSerializable(Tupler[HNil])
    assertSerializable(Tupler[L])

    assertSerializable(Init[L])

    assertSerializable(Last[L])

    assertSerializable(Selector[L, Int])
    assertSerializable(Selector[L, String])

    assertSerializable(Partition[HNil, Int])
    assertSerializable(Partition[L, Int])

    assertSerializable(Filter[HNil, Int])
    assertSerializable(Filter[L, Int])

    assertSerializable(FilterNot[HNil, Int])
    assertSerializable(FilterNot[L, Int])

    assertSerializable(Remove[L, Int])

    assertSerializable(RemoveAll[L, IS])

    assertSerializable(Replacer[L, Int, String])

    assertSerializable(Modifier[L, Int, String])

    assertSerializable(ReplaceAt[L, _1, Double])

    assertSerializable(At[L, _0])
    assertSerializable(At[L, _1])

    assertSerializable(Drop[L, _0])
    assertSerializable(Drop[L, _1])

    assertSerializable(Take[L, _0])
    assertSerializable(Take[L, _1])

    assertSerializable(Split[L, _0])
    assertSerializable(Split[L, _1])

    assertSerializable(ReverseSplit[L, _0])
    assertSerializable(ReverseSplit[L, _1])

    assertSerializable(SplitLeft[L, Int])
    assertSerializable(SplitLeft[L, String])

    assertSerializable(ReverseSplitLeft[L, Int])
    assertSerializable(ReverseSplitLeft[L, String])

    assertSerializable(SplitRight[L, Int])
    assertSerializable(SplitRight[L, String])

    assertSerializable(ReverseSplitRight[L, Int])
    assertSerializable(ReverseSplitRight[L, String])

    assertSerializable(Reverse[HNil])
    assertSerializable(Reverse[L])

    assertSerializable(Align[L, LP])

    assertSerializable(Prepend[HNil, L])
    assertSerializable(Prepend[L, HNil])
    assertSerializable(Prepend[L, LP])

    assertSerializable(ReversePrepend[HNil, L])
    assertSerializable(ReversePrepend[L, HNil])
    assertSerializable(ReversePrepend[L, LP])

    assertSerializable(ZipOne[L, FL])

    assertSerializable(Transposer[HNil])
    assertSerializable(Transposer[FL])

    assertSerializable(Zip[HNil])
    assertSerializable(Zip[FL])

    assertSerializable(Unzip[HNil])
    assertSerializable(Unzip[LT])

    assertSerializable(ZipApply[HNil, HNil])
    assertSerializable(ZipApply[AL, L])

    assertSerializable(ZipConst[Int, L])

    assertSerializable(ZipWith[HNil, HNil, combineR.type])
    assertSerializable(ZipWith[L, I3, combineR.type])

    assertSerializable(ZipWithKeys[HNil, HNil])
    assertSerializable(ZipWithKeys[K, L])

    assertSerializable(Collect[HNil, selInt.type])
    assertSerializable(Collect[L, selInt.type])

    assertSerializable(Ordering[HNil])
    assertSerializable(Ordering[L])

    assertSerializable(MapCons[HNil, HNil])
    assertSerializable(MapCons[L, FL])

    assertSerializable(Interleave[Int, HNil])
    assertSerializable(Interleave[Int, L])

    assertSerializable(FlatMapInterleave[Int, HNil])
    assertSerializable(FlatMapInterleave[Int, FL])

    assertSerializable(Permutations[HNil])
    assertSerializable(Permutations[L])

    assertSerializable(RotateLeft[L, _0])
    assertSerializable(RotateLeft[L, _2])

    assertSerializable(RotateRight[L, _0])
    assertSerializable(RotateRight[L, _2])

    assertSerializable(LeftScanner[HNil, Int, smear.type])
    assertSerializable(LeftScanner[IS, Int, smear.type])

    assertSerializable(RightScanner[HNil, Int, smear.type])
    assertSerializable(RightScanner[IS, Int, smear.type])

    assertSerializable(Fill[_0, Int])
    assertSerializable(Fill[_3, Int])

    assertSerializable(Patcher[_0, _1, L, IS])
  }

  @Test
  def testPoly {
    assertSerializable(poly.identity)
    assertSerializable(isDefined)
    assertSerializable(productElements)
    assertSerializable(smear)
  }

  @Test
  def testNats {
    assertSerializable(_0)
    assertSerializable(_1)
    assertSerializable(_2)
    assertSerializable(_3)
    assertSerializable(_4)
  }

  @Test
  def testFunctions {
    assertSerializable(FnToProduct[() => String])
    assertSerializable(FnToProduct[(Int) => String])
    assertSerializable(FnToProduct[(Int, Boolean) => String])

    assertSerializable(FnFromProduct[(HNil) => String])
    assertSerializable(FnFromProduct[(Int :: HNil) => String])
    assertSerializable(FnFromProduct[(Int :: Boolean :: HNil) => String])
  }

  @Test
  def testGeneric {
    assertSerializable(Generic[(Int, String, Boolean)])
    assertSerializable(Generic[Option[Int]])

    assertSerializable(DefaultSymbolicLabelling[(Int, String, Boolean)])
    assertSerializable(DefaultSymbolicLabelling[Option[Int]])

    assertSerializable(LabelledGeneric[(Int, String, Boolean)])
    assertSerializable(LabelledGeneric[Option[Int]])
  }
}
