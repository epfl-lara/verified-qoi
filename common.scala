import stainless.*
import stainless.lang.*
import stainless.collection.*
import stainless.annotation.{opaque, pure, inlineOnce}
import stainless.proof.*

object common {
  val OpIndex = 0x00
  val OpDiff = 0x40
  val OpLuma = 0x80
  val OpRun = 0xc0
  val OpRgb = 0xfe
  val OpRgba = 0xff

  val Mask2 = 0xc0

  //  val MagicNumber = ('q'.toByte << 24) | ('o'.toByte << 16) | ('i'.toByte << 8) | 'f'.toByte
  val MagicNumber = 1903126886
  val HeaderSize = 14
  val Padding = 8

  object Pixel {
    def r(px: Int): Byte = ((px >> 24) & 0xff).toByte
    def g(px: Int): Byte = ((px >> 16) & 0xff).toByte
    def b(px: Int): Byte = ((px >> 8) & 0xff).toByte
    def a(px: Int): Byte = (px & 0xff).toByte

    def fromRgba(r: Byte, g: Byte, b: Byte, a: Byte): Int =
      (r << 24) | ((g << 16) & 0xffffff) | ((b << 8) & 0xffff) | (a.toInt & 0xff)

    def incremented(px: Int)(r: Byte = 0, g: Byte = 0, b: Byte = 0, a: Byte = 0): Int =
      fromRgba(((Pixel.r(px) + r) & 0xff).toByte, ((Pixel.g(px) + g) & 0xff).toByte, ((Pixel.b(px) + b) & 0xff).toByte, ((Pixel.a(px) + a) & 0xff).toByte)

    def withRgba(px: Int)(r: Byte = Pixel.r(px), g: Byte = Pixel.g(px), b: Byte = Pixel.b(px), a: Byte = Pixel.a(px)): Int =
      fromRgba(r, g, b, a)
  }

  def colorPos(px: Int): Int = {
    ((Pixel.r(px) & 0xff) * 3 + (Pixel.g(px) & 0xff) * 5 + (Pixel.b(px) & 0xff) * 7 + (Pixel.a(px) & 0xff) * 11) % 64
  }.ensuring(x => x >= 0 && x < 64)

  def write16(data: Array[Byte], i: Int, value: Short): Unit = {
    require(data.length >= 2 && i >= 0 && i < data.length - 1)
    data(i) = ((0xff00 & value) >> 8).toByte
    data(i + 1) = (0xff & value).toByte
  } ensuring(_ => read16(data, i) == value && old(data).length == data.length)

  def write32(data: Array[Byte], i: Int, value: Int): Unit = {
    require(data.length >= 4 && i >= 0 && i < data.length - 3)
    write16(data, i, (value >> 16).toShort)
    write16(data, i + 2, value.toShort)
  } ensuring(_ => read32(data, i) == value && old(data).length == data.length)

  def read16(data: Array[Byte], i: Int): Short = {
    require(data.length >= 2 && i >= 0 && i < data.length - 1)
    (((((data(i) & 0xff) << 8) & 0xffff) | (data(i + 1) & 0xff)) & 0xffff).toShort
  }

  def read32(data: Array[Byte], i: Int): Int = {
    require(data.length >= 4 && i >= 0 && i < data.length - 3)
    (read16(data, i) << 16) | (read16(data, i + 2) & 0xffff)
  }

  @inline
  def bool2int(b: Boolean): Int = if (b) 1 else 0

  // TODO: :)
  @opaque
  @inlineOnce
  def sorry(b: Boolean): Unit = {
    ??? : Unit
  }.ensuring(_ => b)

  // OK
  @opaque
  @inlineOnce
  def modSumLemma(x: Long, chan: Long): Unit = {
    require(0 <= x && x <= Long.MaxValue - chan)
    require(3 <= chan && chan <= 4)
    require(x % chan == 0)
  }.ensuring(_ => (x + chan) % chan == 0)

  // OK
  @opaque
  @inlineOnce
  def modLeqLemma(x: Long, y: Long, chan: Long): Unit = {
    require(y >= 0)
    require(0 <= x && x < y)
    require(3 <= chan && chan <= 4)
    require(x % chan == 0)
    require(y % chan == 0)
  }.ensuring(_ => x + chan <= y)

  // OK
  @opaque
  @inlineOnce
  def modLtLemma(x: Long, y: Long, chan: Long): Unit = {
    require(y >= 0)
    require(3 <= chan && chan <= 4)
    require(0 <= x && x <= Long.MaxValue - chan)
    require(x + chan <= y)
    require(x % chan == 0)
    require(y % chan == 0)
  }.ensuring(_ => x < y)

  // OK
  @pure
  def samePixels(pixels: Array[Byte], px: Int, pxPos: Long, chan: Long): Boolean = {
    require(3 <= chan && chan <= 4)
    require(pixels.length % chan == 0)
    require(0 <= pxPos && pxPos < pixels.length)
    require(pxPos % chan == 0)

    modLeqLemma(pxPos, pixels.length, chan)
    assert(pxPos + chan <= pixels.length)

    pixels(pxPos.toInt) == Pixel.r(px) &&
    pixels(pxPos.toInt + 1) == Pixel.g(px) &&
    pixels(pxPos.toInt + 2) == Pixel.b(px) &&
    ((chan == 4) ==> (pixels(pxPos.toInt + 3) == Pixel.a(px)))
  }

  // OK
  @pure
  @opaque
  @inlineOnce
  def samePixelsSingleElementRange(pixels: Array[Byte], px: Int, pxPos: Long, chan: Long): Unit = {
    require(3 <= chan && chan <= 4)
    require(0 <= pxPos && pxPos < pixels.length)
    require(pxPos % chan == 0 && pixels.length % chan == 0)
    require(samePixels(pixels, px, pxPos, chan))
  }.ensuring(_ => samePixelsForall(pixels, px, pxPos, pxPos + chan, chan))

  // OK
  @pure
  @opaque
  @inlineOnce
  def samePixelsExtendedRangeLemma(pixels: Array[Byte], px: Int, pxPosStart: Long, pxPosEnd: Long, chan: Long): Unit = {
    decreases(pxPosEnd - pxPosStart)
    require(3 <= chan && chan <= 4)
    require(pixels.length % chan == 0)
    require(0 <= pxPosStart && pxPosStart < pxPosEnd)
    require(pxPosEnd < pixels.length)
    require(pxPosStart % chan == 0)
    require(pxPosEnd % chan == 0)
    require(samePixelsForall(pixels, px, pxPosStart, pxPosEnd, chan))
    require(samePixels(pixels, px, pxPosEnd, chan))

    modSumLemma(pxPosEnd, chan)
    modLeqLemma(pxPosStart, pxPosEnd, chan)
    modLeqLemma(pxPosEnd, pixels.length, chan)
    assert((pxPosStart + chan) % chan == 0)
    assert(pxPosStart + chan <= pxPosEnd)
    assert(pxPosEnd + chan <= pixels.length)

    if (pxPosStart + chan == pxPosEnd) {
      check(samePixelsForall(pixels, px, pxPosStart, pxPosEnd + chan, chan))
    } else {
      samePixelsExtendedRangeLemma(pixels, px, pxPosStart + chan, pxPosEnd, chan)
      assert(samePixelsForall(pixels, px, pxPosStart + chan, pxPosEnd + chan, chan))
      check(samePixelsForall(pixels, px, pxPosStart, pxPosEnd + chan, chan))
    }
  }.ensuring { _ =>
    modSumLemma(pxPosEnd, chan)
    modLeqLemma(pxPosEnd, pixels.length, chan)
    samePixelsForall(pixels, px, pxPosStart, pxPosEnd + chan, chan)
  }

  // OK
  @pure
  def samePixelsForall(pixels: Array[Byte], px: Int, pxPosStart: Long, pxPosEnd: Long, chan: Long): Boolean = {
    decreases(pxPosEnd - pxPosStart)
    require(3 <= chan && chan <= 4)
    require(pixels.length % chan == 0)
    require(0 <= pxPosStart && pxPosStart < pxPosEnd)
    require(pxPosEnd <= pixels.length)
    require(pxPosEnd % chan == 0)
    require(pxPosStart % chan == 0)

    modLeqLemma(pxPosStart, pxPosEnd, chan)
    assert(pxPosStart + chan <= pxPosEnd)

    samePixels(pixels, px, pxPosStart, chan) &&
      (if (pxPosStart + chan == pxPosEnd) true
      else {
        assert(pxPosStart + chan <= pxPosEnd)
        modSumLemma(pxPosStart, chan)
        assert((pxPosStart + chan) % chan == 0)
        assert(pixels.length % chan == 0)
        samePixelsForall(pixels, px, pxPosStart + chan, pxPosEnd, chan)
      })
    // forall[Int](i => (pxPosStart / chan <= i && i < pxPosEnd / chan) ==> samePixels(pixels, px, chan * i))
  }

  // OK
  @pure
  @opaque
  @inlineOnce
  def samePixelsForallCombinedLemma(pixels: Array[Byte], px: Int, pxPosStart: Long, pxMiddle: Long, pxPosEnd: Long, chan: Long): Unit = {
    decreases(pxPosEnd - pxPosStart)
    require(3 <= chan && chan <= 4)
    require(0 <= pxPosStart && pxPosStart < pxMiddle && pxMiddle < pxPosEnd)
    require(pixels.length % chan == 0)
    require(pxPosEnd <= pixels.length)
    require(pxPosEnd % chan == 0)
    require(pxMiddle % chan == 0)
    require(pxPosStart % chan == 0)
    require(samePixelsForall(pixels, px, pxPosStart, pxMiddle, chan))
    require(samePixelsForall(pixels, px, pxMiddle, pxPosEnd, chan))

    if (pxMiddle == pxPosStart + chan) {
      check(samePixelsForall(pixels, px, pxPosStart, pxPosEnd, chan))
    } else {
      assert(samePixelsForall(pixels, px, pxPosStart + chan, pxMiddle, chan))
      samePixelsForallCombinedLemma(pixels, px, pxPosStart + chan, pxMiddle, pxPosEnd, chan)
      assert(samePixelsForall(pixels, px, pxPosStart + chan, pxPosEnd, chan))
      check(samePixelsForall(pixels, px, pxPosStart, pxPosEnd, chan))
    }
  }.ensuring(_ => samePixelsForall(pixels, px, pxPosStart, pxPosEnd, chan))

  // OK
  @pure
  @opaque
  @inlineOnce
  def samePixelsForallArraysEq(pixels1: Array[Byte], pixels2: Array[Byte], px: Int, pxPosStart: Long, pxPosEnd: Long, chan: Long): Unit = {
    decreases(pxPosEnd - pxPosStart)
    require(3 <= chan && chan <= 4)
    require(0 <= pxPosStart && pxPosStart < pxPosEnd && pxPosEnd <= pixels1.length)
    require(pixels1.length % chan == 0)
    require(pxPosStart % chan == 0)
    require(pxPosEnd % chan == 0)
    require(pixels1.length == pixels2.length)
    require(samePixelsForall(pixels1, px, pxPosStart, pxPosEnd, chan))
    require(samePixelsForall(pixels2, px, pxPosStart, pxPosEnd, chan))

    assert(samePixels(pixels1, px, pxPosStart, chan))
    assert(samePixels(pixels2, px, pxPosStart, chan))
    if (pxPosStart + chan == pxPosEnd) {
      check(arraysEq(pixels1, pixels2, pxPosStart, pxPosEnd))
    } else {
      modSumLemma(pxPosStart, chan)
      modLtLemma(pxPosStart, pxPosEnd, chan)
      samePixelsForallArraysEq(pixels1, pixels2, px, pxPosStart + chan, pxPosEnd, chan)
      assert(arraysEq(pixels1, pixels2, pxPosStart + chan, pxPosEnd))
      assert(arraysEq(pixels1, pixels2, pxPosStart, pxPosStart + chan))
      arraysEqCombinedLemma(pixels1, pixels2, pxPosStart, pxPosStart + chan, pxPosEnd)
      check(arraysEq(pixels1, pixels2, pxPosStart, pxPosEnd))
    }
  }.ensuring(_ => arraysEq(pixels1, pixels2, pxPosStart, pxPosEnd))

  // OK
  @pure
  @opaque
  @inlineOnce
  def samePixelsForallUnchangedLemma(pixels1: Array[Byte], pixels2: Array[Byte], px: Int, pxPosStart: Long, pxPosEnd: Long, chan: Long): Unit = {
    decreases(pxPosEnd - pxPosStart)
    require(3 <= chan && chan <= 4)
    require(0 <= pxPosStart && pxPosStart < pxPosEnd && pxPosEnd <= pixels1.length)
    require(pixels1.length % chan == 0)
    require(pxPosStart % chan == 0)
    require(pxPosEnd % chan == 0)
    require(pixels1.length == pixels2.length)
    require(samePixelsForall(pixels1, px, pxPosStart, pxPosEnd, chan))
    require(arraysEq(pixels1, pixels2, pxPosStart, pxPosEnd))

    assert(samePixels(pixels2, px, pxPosStart, chan))
    if (pxPosStart + chan == pxPosEnd) {
      check(samePixelsForall(pixels2, px, pxPosStart, pxPosEnd, chan))
    } else {
      modSumLemma(pxPosStart, chan)
      modLtLemma(pxPosStart, pxPosEnd, chan)
      assert(samePixelsForall(pixels1, px, pxPosStart + chan, pxPosEnd, chan))
      arraysEqDropLeftLemma(pixels1, pixels2, pxPosStart, pxPosStart + chan, pxPosEnd)
      assert(arraysEq(pixels1, pixels2, pxPosStart + chan, pxPosEnd))
      assert(pxPosStart + chan < pxPosEnd)
      assert((pxPosStart + chan) % chan == 0)
      samePixelsForallUnchangedLemma(pixels1, pixels2, px, pxPosStart + chan, pxPosEnd, chan)
      check(samePixelsForall(pixels2, px, pxPosStart, pxPosEnd, chan))
    }
  }.ensuring(_ => samePixelsForall(pixels2, px, pxPosStart, pxPosEnd, chan))


  // OK
  @pure
  def arraysEq[T](arr1: Array[T], arr2: Array[T], from: Long, until: Long): Boolean = {
    decreases(until - from)
    require(arr1.length == arr2.length)
    require(0 <= from && from <= until && until <= arr1.length)
    if (from == until) true
    else arr1(from.toInt) == arr2(from.toInt) && arraysEq(arr1, arr2, from + 1, until)
  }

  // OK
  @pure
  @opaque
  @inlineOnce
  def arraysEqCombinedLemma[T](arr1: Array[T], arr2: Array[T], from: Long, middle: Long, to: Long): Unit = {
    decreases(to - from)
    require(arr1.length == arr2.length)
    require(0 <= from && from < middle && middle < to && to <= arr1.length)
    require(arraysEq(arr1, arr2, from, middle))
    require(arraysEq(arr1, arr2, middle, to))

    if (middle == from + 1) {
      check(arraysEq(arr1, arr2, from, to))
    } else {
      assert(arraysEq(arr1, arr2, from + 1, middle))
      arraysEqCombinedLemma(arr1, arr2, from + 1, middle, to)
      assert(arraysEq(arr1, arr2, from + 1, to))
      check(arraysEq(arr1, arr2, from, to))
    }
  }.ensuring(_ => arraysEq(arr1, arr2, from, to))

  // OK
  @pure
  @opaque
  @inlineOnce
  def arraysEqCombinedLemma2[T](arr1: Array[T], arr2: Array[T], from: Long, middle: Long, to: Long): Unit = {
    decreases(to - from)
    require(arr1.length == arr2.length)
    require(0 <= from && from <= middle && middle <= to && to <= arr1.length)
    require(from < to)
    require(arraysEq(arr1, arr2, from, middle))
    require(arraysEq(arr1, arr2, middle, to))

    if (from == middle || middle == to) {
      check(arraysEq(arr1, arr2, from, to))
    } else {
      arraysEqCombinedLemma(arr1, arr2, from, middle, to)
      check(arraysEq(arr1, arr2, from, to))
    }
  }.ensuring(_ => arraysEq(arr1, arr2, from, to))

  // OK
  @pure
  @opaque
  @inlineOnce
  def arraysEqAtIndex[T](arr1: Array[T], arr2: Array[T], from: Long, to: Long, at: Long): Unit = {
    decreases(to - at)
    require(arr1.length == arr2.length)
    require(0 <= from && from <= to && to <= arr1.length)
    require(arraysEq(arr1, arr2, from, to))
    require(from <= at && at < to)
    if (at == from) {
      check(arr1(at.toInt) == arr2(at.toInt))
    } else {
      arraysEqAtIndex(arr1, arr2, from + 1, to, at)
      check(arr1(at.toInt) == arr2(at.toInt))
    }
  }.ensuring(_ => arr1(at.toInt) == arr2(at.toInt))

  // OK
  @pure
  @opaque
  @inlineOnce
  def arraysEqSymLemma[T](arr1: Array[T], arr2: Array[T], from: Long, to: Long): Unit = {
    decreases(to - from)
    require(arr1.length == arr2.length)
    require(0 <= from && from <= to && to <= arr1.length)
    require(arraysEq(arr1, arr2, from, to))
    if (from == to) {
      check(arraysEq(arr2, arr1, from, to))
    } else {
      arraysEqSymLemma(arr1, arr2, from + 1, to)
      check(arraysEq(arr2, arr1, from, to))
    }
  }.ensuring(_ => arraysEq(arr2, arr1, from, to))

  // OK
  @pure
  @opaque
  @inlineOnce
  def arraysEqDropRightLemma[T](arr1: Array[T], arr2: Array[T], from: Long, middle: Long, to: Long): Unit = {
    decreases(to - from)
    require(arr1.length == arr2.length)
    require(0 <= from && from <= middle && middle <= to && to <= arr1.length)
    require(arraysEq(arr1, arr2, from, to))

    if (middle == from) {
      check(arraysEq(arr1, arr2, from, to))
    } else {
      arraysEqDropRightLemma(arr1, arr2, from + 1, middle, to)
      check(arraysEq(arr1, arr2, from, middle))
    }
  }.ensuring(_ => arraysEq(arr1, arr2, from, middle))

  // OK
  @pure
  @opaque
  @inlineOnce
  def arraysEqDropLeftLemma[T](arr1: Array[T], arr2: Array[T], from: Long, middle: Long, to: Long): Unit = {
    decreases(to - from)
    require(arr1.length == arr2.length)
    require(0 <= from && from <= middle && middle <= to && to <= arr1.length)
    require(arraysEq(arr1, arr2, from, to))

    if (middle == from) {
      check(arraysEq(arr1, arr2, middle, to))
    } else {
      arraysEqDropLeftLemma(arr1, arr2, from + 1, middle, to)
      check(arraysEq(arr1, arr2, middle, to))
    }
  }.ensuring(_ => arraysEq(arr1, arr2, middle, to))

  // OK
  @pure
  @opaque
  @inlineOnce
  def arraysEqTransLemma[T](arr1: Array[T], arr2: Array[T], arr3: Array[T], from: Long, to: Long): Unit = {
    decreases(to - from)
    require(arr1.length == arr2.length && arr2.length == arr3.length)
    require(0 <= from && from <= to && to <= arr1.length)
    require(arraysEq(arr1, arr2, from, to))
    require(arraysEq(arr2, arr3, from, to))

    if (from == to) {
      check(arraysEq(arr1, arr3, from, to))
    } else {
      arraysEqTransLemma(arr1, arr2, arr3, from + 1, to)
      check(arraysEq(arr1, arr3, from, to))
    }
  }.ensuring(_ => arraysEq(arr1, arr3, from, to))

  // OK
  @pure
  @opaque
  @inlineOnce
  def eqImpliesArraysEq[T](arr1: Array[T], arr2: Array[T], from: Long, to: Long): Unit = {
    decreases(to - from)
    require(arr1 == arr2)
    require(0 <= from && from <= to && to <= arr1.length)

    if (from == to) {
      check(arraysEq(arr1, arr2, from, to))
    } else {
      eqImpliesArraysEq(arr1, arr2, from + 1, to)
      check(arraysEq(arr1, arr2, from, to))
    }
  }.ensuring(_ => arraysEq(arr1, arr2, from, to))

  // OK
  @pure
  @opaque
  @inlineOnce
  def updatedAtArraysEq[T](arr: Array[T], i: Long, t: T): Unit = {
    require(0 <= i && i < arr.length)
    val upd = arr.updated(i.toInt, t)

    {
      updatedAtArraysEqLeftProof(arr, i, t, 0)
      updatedAtArraysEqRightProof(arr, i, t, arr.length)
    }.ensuring { _ =>
      arraysEq(arr, upd, 0, i) &&&
      arraysEq(arr, upd, i + 1, arr.length)
    }
  }

  // OK
  @pure
  @opaque
  @inlineOnce
  def updatedAtArraysEqLeftProof[T](arr: Array[T], i: Long, t: T, j: Long): Unit = {
    decreases(i - j)
    require(0 <= i && i < arr.length)
    require(0 <= j && j <= i)
    val upd = arr.updated(i.toInt, t)

    {
      if (i == j) {
        check(arraysEq(arr, upd, j, i))
      } else {
        updatedAtArraysEqLeftProof(arr, i, t, j + 1)
        check(arraysEq(arr, upd, j, i))
      }
    }.ensuring(_ => arraysEq(arr, upd, j, i))
  }

  // OK
  @pure
  @opaque
  @inlineOnce
  def updatedAtArraysEqRightProof[T](arr: Array[T], i: Long, t: T, j: Long): Unit = {
    decreases(j - i)
    require(0 <= i && i < arr.length)
    require(i < j && j <= arr.length)
    val upd = arr.updated(i.toInt, t)

    {
      if (i + 1 == j) {
        check(arraysEq(arr, upd, i + 1, j))
      } else {
        updatedAtArraysEqRightProof(arr, i, t, j - 1)
        assert(arraysEq(arr, upd, i + 1, j - 1))
        assert(arraysEq(arr, upd, j - 1, j))
        arraysEqCombinedLemma2(arr, upd, i + 1, j - 1, j)
        check(arraysEq(arr, upd, i + 1, j))
      }
    }.ensuring(_ => arraysEq(arr, upd, i + 1, j))
  }

  // OK
  @pure
  @opaque
  @inlineOnce
  def updatedAtArraysEq[T](arr: Array[T], i: Long, t1: T, t2: T): Unit = {
    require(0 <= i && i < arr.length)
    require(i + 1 < arr.length)
    val upd = arr.updated(i.toInt, t1).updated(i.toInt + 1, t2)

    {
      val updt1 = arr.updated(i.toInt, t1)
      updatedAtArraysEq(arr, i, t1)
      assert(arraysEq(arr, updt1, 0, i))

      updatedAtArraysEq(updt1, i + 1, t2)
      assert(arraysEq(updt1, upd, 0, i + 1))

      arraysEqDropRightLemma(updt1, upd, 0, i, i + 1)
      arraysEqTransLemma(arr, updt1, upd, 0, i)
      check(arraysEq(arr, upd, 0, i))
    }.ensuring { _ =>
      arraysEq(arr, upd, 0, i)
    }
  }

  // OK
  @pure
  @opaque
  @inlineOnce
  def updatedAtArraysEq[T](arr: Array[T], i: Long, t1: T, t2: T, t3: T): Unit = {
    require(0 <= i && i < arr.length)
    require(i + 1 < arr.length)
    require(i + 2 < arr.length)
    val upd = arr.updated(i.toInt, t1).updated(i.toInt + 1, t2).updated(i.toInt + 2, t3)

    {
      val updt1t2 = arr.updated(i.toInt, t1).updated(i.toInt + 1, t2)
      updatedAtArraysEq(arr, i, t1, t2)
      assert(arraysEq(arr, updt1t2, 0, i))

      updatedAtArraysEq(updt1t2, i + 2, t3)
      assert(arraysEq(updt1t2, upd, 0, i + 2))

      arraysEqDropRightLemma(updt1t2, upd, 0, i, i + 2)
      arraysEqTransLemma(arr, updt1t2, upd, 0, i)
      check(arraysEq(arr, upd, 0, i))
    }.ensuring { _ =>
      arraysEq(arr, upd, 0, i)
    }
  }

  // OK
  @pure
  @opaque
  @inlineOnce
  def updatedAtArraysEq[T](arr: Array[T], i: Long, t1: T, t2: T, t3: T, t4: T): Unit = {
    require(0 <= i && i < arr.length)
    require(i + 1 < arr.length)
    require(i + 2 < arr.length)
    require(i + 3 < arr.length)
    val upd = arr.updated(i.toInt, t1).updated(i.toInt + 1, t2).updated(i.toInt + 2, t3).updated(i.toInt + 3, t4)

    {
      val updt1t2t3 = arr.updated(i.toInt, t1).updated(i.toInt + 1, t2).updated(i.toInt + 2, t3)
      updatedAtArraysEq(arr, i, t1, t2, t3)
      assert(arraysEq(arr, updt1t2t3, 0, i))

      updatedAtArraysEq(updt1t2t3, i + 3, t4)
      assert(arraysEq(updt1t2t3, upd, 0, i + 3))

      arraysEqDropRightLemma(updt1t2t3, upd, 0, i, i + 3)
      arraysEqTransLemma(arr, updt1t2t3, upd, 0, i)
      check(arraysEq(arr, upd, 0, i))
    }.ensuring { _ =>
      arraysEq(arr, upd, 0, i)
    }
  }

  // OK
  @pure
  @opaque
  @inlineOnce
  def updatedAtArraysEq[T](arr: Array[T], i: Long, t1: T, t2: T, t3: T, t4: T, t5: T): Unit = {
    require(0 <= i && i < arr.length)
    require(i + 1 < arr.length)
    require(i + 2 < arr.length)
    require(i + 3 < arr.length)
    require(i + 4 < arr.length)
    val upd = arr.updated(i.toInt, t1).updated(i.toInt + 1, t2).updated(i.toInt + 2, t3).updated(i.toInt + 3, t4).updated(i.toInt + 4, t5)

    {
      val updt1t2t3t4 = arr.updated(i.toInt, t1).updated(i.toInt + 1, t2).updated(i.toInt + 2, t3).updated(i.toInt + 3, t4)
      updatedAtArraysEq(arr, i, t1, t2, t3, t4)
      assert(arraysEq(arr, updt1t2t3t4, 0, i))

      updatedAtArraysEq(updt1t2t3t4, i + 4, t5)
      assert(arraysEq(updt1t2t3t4, upd, 0, i + 4))

      arraysEqDropRightLemma(updt1t2t3t4, upd, 0, i, i + 4)
      arraysEqTransLemma(arr, updt1t2t3t4, upd, 0, i)
      check(arraysEq(arr, upd, 0, i))
    }.ensuring { _ =>
      arraysEq(arr, upd, 0, i)
    }
  }

}
