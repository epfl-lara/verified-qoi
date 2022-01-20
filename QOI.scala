// Adapted from Dominic Szablewski
// https://phoboslab.org/log/2021/11/qoi-fast-lossless-image-compression

import stainless.*
import stainless.lang.*
import stainless.collection.*
import stainless.annotation.{inlineOnce, mutable, opaque, pure}
import stainless.proof.*

object QOI {
  val Index = 0x00
  val Run8 = 0x40
  val Run16 = 0x60
  val Diff8 = 0x80
  val Diff16 = 0xc0
  val Diff24 = 0xe0
  val Color = 0xf0

  val Mask2 = 0xc0
  val Mask3 = 0xe0
  val Mask4 = 0xf0

  val MagicNumber = 1903126886
  val HeaderSize = 12
  val Padding = 4

  opaque type Pixel = Int
  object Pixel {
    def fromInt(v: Int): Pixel = v
    def fromRgba(r: Byte, g: Byte, b: Byte, a: Byte): Pixel =
      (r << 24) | ((g << 16) & 0xffffff) | ((b << 8) & 0xffff) | (a.toInt & 0xff)

    extension (p: Pixel) {
      def toInt: Int = p

      def r: Byte = ((p >> 24) & 0xff).toByte
      def g: Byte = ((p >> 16) & 0xff).toByte
      def b: Byte = ((p >> 8) & 0xff).toByte
      def a: Byte = (p & 0xff).toByte

      def incremented(r: Byte = 0, g: Byte = 0, b: Byte = 0, a: Byte = 0): Pixel =
        fromRgba(((p.r + r) & 0xff).toByte, ((p.g + g) & 0xff).toByte, ((p.b + b) & 0xff).toByte, ((p.a + a) & 0xff).toByte)

      def withRgba(r: Byte = p.r, g: Byte = p.g, b: Byte = p.b, a: Byte = p.a): Pixel =
        fromRgba(r, g, b, a)
    }
  }
  import Pixel._

  def colorPos(px: Pixel): Int = {
    ((px.r ^ px.g ^ px.b ^ px.a) & 0xff) % 64
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

  case class RunUpdate(reset: Boolean, run: Long, outPos: Long)

  case class LoopIter(px: Pixel, pxPrev: Pixel, pxPos: Long)

  def encode(pixels: Array[Byte], w: Long, h: Long, chan: Long): Unit = {
    require(w > 0 && h > 0 && w < 8192 && h < 8192)
    require(3 <= chan && chan <= 4)
    require(w * h * chan == pixels.length)
    val maxSize = w * h * (chan + 1) + HeaderSize + Padding
    val pxEnd = pixels.length - chan

    def positionsIneqInv(run: Long, outPos: Long, pxPos: Long): Boolean =
      chan * (outPos - HeaderSize + chan * run) <= (chan + 1) * pxPos

    def rangesInv(indexLen: Long, bytesLen: Long, run: Long, outPos: Long, pxPos: Long): Boolean =
      0 <= pxPos && pxPos <= pixels.length &&
        ((pxPos % chan) == 0) &&
        w * h * chan == pixels.length &&
        0 <= run && run < 0x2020 &&
        HeaderSize <= outPos && outPos <= maxSize &&
        bytesLen == maxSize &&
        indexLen == 64

    @opaque
    @inlineOnce
    def withinBoundsLemma(indexLen: Long, bytesLen: Long, run: Long, outPos: Long, pxPos: Long): Unit = {
      require(rangesInv(indexLen, bytesLen, run, outPos, pxPos))
      require(positionsIneqInv(run, outPos, pxPos))
      require(pxPos + chan <= pixels.length)
      assert(chan * (outPos - HeaderSize + chan * run + chan + 1) <= (chan + 1) * (pxPos + chan))
      assert(chan * (outPos - HeaderSize + chan * run + chan + 1) <= (chan + 1) * pixels.length)
      assert((chan + 1) * pixels.length == chan * (maxSize - HeaderSize - Padding))
    }.ensuring(_ => outPos + run * chan + chan + 1 <= maxSize)

    @opaque
    @inlineOnce
    def positionsIneqIncrementedLemma(indexLen: Long, bytesLen: Long, run: Long, outPos: Long, pxPos: Long): Unit = {
      require(rangesInv(indexLen, bytesLen, run, outPos, pxPos))
      require(positionsIneqInv(run, outPos, pxPos))
    }.ensuring(_ => positionsIneqInv(run, outPos + chan + 1, pxPos + chan))

    @opaque
    @inlineOnce
    def loopInvUpperOutPosLemma(indexLen: Long, bytesLen: Long, run: Long, oldOutPos: Long, pxPos: Long, newOutPos: Long): Unit = {
      require(rangesInv(indexLen, bytesLen, run, oldOutPos, pxPos))
      require(HeaderSize <= newOutPos && newOutPos <= oldOutPos + chan + 1)
      require(positionsIneqInv(run, oldOutPos + chan + 1, pxPos))
      assert(chan * ((oldOutPos - HeaderSize) + chan * run) <= (chan + 1) * pxPos)
      assert(chan * (newOutPos - HeaderSize) <= chan * (oldOutPos + chan + 1 - HeaderSize))
      assert(chan * ((newOutPos - HeaderSize) + chan * run) <= chan * ((oldOutPos + chan + 1 - HeaderSize) + chan * run))
    }.ensuring(_ => positionsIneqInv(run, newOutPos, pxPos))

    //////////////////////////////////////////////////////////////////////////////////

    @opaque
    @inlineOnce
    def loop(index: Array[Pixel], bytes: Array[Byte], pxPrev: Pixel, run0: Long, outPos0: Long, pxPos: Long): Long = {
      require(rangesInv(index.length, bytes.length, run0, outPos0, pxPos))
      require(pxPos + chan <= pixels.length)
      require(positionsIneqInv(run0, outPos0, pxPos))
      require((chan == 3) ==> (pxPrev.a == 255.toByte))

      val px =
        if (chan == 4) Pixel.fromInt(read32(pixels, pxPos.toInt))
        else {
          assert(chan == 3 && pxPrev.a == 255.toByte)
          Pixel.fromRgba(pixels(pxPos.toInt), pixels(pxPos.toInt + 1), pixels(pxPos.toInt + 2), pxPrev.a)
        }
      assert((chan == 3) ==> (px.a == pxPrev.a))
      given li: LoopIter = LoopIter(px, pxPrev, pxPos)

      val runUpd = updateRun(index, bytes, run0, outPos0)
      val run1 = runUpd.run
      val outPos1 = runUpd.outPos

      val outPos2 = if (px != pxPrev) {
        ghost {
          if (run1 != 0) {
            assert(run1 > 0)
            check(positionsIneqInv(run1, outPos1 + chan + 1, pxPos + chan))
          } else if (run0 == 0) {
            assert(run1 == 0)
            check(positionsIneqInv(run1, outPos1 + chan + 1, pxPos + chan))
          } else {
            assert(runUpd.reset && outPos1 <= outPos0 + 2 && run0 > 0 && run1 == 0)
            assert(chan * (outPos0 - HeaderSize + chan) <= (chan + 1) * pxPos)
            assert(chan * (outPos0 - HeaderSize + chan) + (chan + 1) * chan <= (chan + 1) * pxPos + (chan + 1) * chan)
            assert(chan * (outPos0 - HeaderSize + chan + chan + 1) <= (chan + 1) * (pxPos + chan))
            assert((chan * (outPos1 - HeaderSize) <= (chan + 1) * (pxPos + chan)) because (chan >= 0 && outPos1 <= outPos0 + 2))
            assert(positionsIneqInv(run1, outPos1, pxPos + chan))
            assert(chan * ((outPos0 - HeaderSize) + chan * run0) <= (chan + 1) * pxPos)
            assert(chan * ((outPos0 - HeaderSize) + chan * run0) + (chan + 1) * chan <= (chan + 1) * pxPos + (chan + 1) * chan)
            assert(chan * ((outPos0 - HeaderSize) + chan * run0 + chan + 1) <= (chan + 1) * (pxPos + chan))
            assert(chan * ((outPos0 - HeaderSize) + chan + 1) <= chan * ((outPos0 - HeaderSize) + chan * run0 + chan + 1))
            check(positionsIneqInv(run1, outPos1 + chan + 1, pxPos + chan))
          }
          assert(positionsIneqInv(run1, outPos1 + chan + 1, pxPos + chan))
        }
        val outPos2 = mainBody(index, bytes, run1, outPos1)
        check(positionsIneqInv(run1, outPos2, li.pxPos + chan))
        assert(HeaderSize <= outPos2 && outPos2 <= maxSize)
        check(rangesInv(index.length, bytes.length, run1, outPos1, pxPos))
        outPos2
      } else {
        ghost {
          if (runUpd.reset) {
            assert(outPos1 <= outPos0 + 2)
            assert(run1 == 0)
            assert(chan * (outPos0 - HeaderSize + run0 * chan) <= (chan + 1) * pxPos)
            assert(chan * (outPos0 - HeaderSize + run0 * chan) + (chan + 1) * chan <= (chan + 1) * pxPos + (chan + 1) * chan)
            assert(chan * (outPos0 - HeaderSize + run0 * chan + chan + 1) <= (chan + 1) * (pxPos + chan))
            assert(chan * (outPos1 - HeaderSize) <= (chan + 1) * (pxPos + chan))
            check(positionsIneqInv(run1, outPos1, pxPos + chan))
          } else {
            assert(outPos1 == outPos0 && run1 == run0 + 1 && run0 <= 0x2020)
            assert(positionsIneqInv(run0, outPos0, pxPos))
            assert(chan * ((outPos0 - HeaderSize) + chan * run0) <=
            (chan + 1) * pxPos + (chan + 1) * chan)
            assert(chan * ((outPos0 - HeaderSize) + chan * (run0 + 1)) <=
            (chan + 1) * pxPos + (chan + 1) * chan)
            assert((
              chan * ((outPos1 - HeaderSize) + chan * (run0 + 1)) <=
              (chan + 1) * pxPos + (chan + 1) * chan) because (outPos1 == outPos0))
            assert((chan * ((outPos1 - HeaderSize) + chan * (run0 + 1)) <= (chan + 1) * (pxPos + chan)) because ((chan + 1) * pxPos + (chan + 1) * chan == (chan + 1) * (pxPos + chan)))
            check(positionsIneqInv(run1, outPos1, pxPos + chan) because (run1 == run0 + 1))
          }
        }
        check(rangesInv(index.length, bytes.length, run1, outPos1, pxPos))
        check(positionsIneqInv(run1, outPos1, pxPos + chan))
        outPos1
      }
      assert(rangesInv(index.length, bytes.length, run1, outPos2, pxPos))
      assert(positionsIneqInv(run1, outPos2, pxPos + chan))

      if (pxPos + chan < pixels.length) {
        loop(index, bytes, px, run1, outPos2, pxPos + chan)
      } else outPos2
    }.ensuring(outPos => HeaderSize <= outPos && outPos <= maxSize && bytes.length == maxSize && index.length == 64)

    @inline
    def updateRun(index: Array[Pixel], bytes: Array[Byte], run0: Long, outPos0: Long)(using li: LoopIter): RunUpdate = {
      require(rangesInv(index.length, bytes.length, run0, outPos0, li.pxPos))
      require(li.pxPos + chan <= pixels.length)
      require(positionsIneqInv(run0, outPos0, li.pxPos))
      import li._

      withinBoundsLemma(index.length, bytes.length, run0, outPos0, pxPos)
      assert(outPos0 + run0 * chan + Padding <= maxSize)
      assert(outPos0 + 2 <= maxSize)

      var run = run0
      var outPos = outPos0

      if (px == pxPrev)
        run += 1

      var runReset = false
      if (run > 0 && (run == 0x2020 || px != pxPrev || pxPos == pxEnd)) {
        if (run < 33) {
          run -= 1
          bytes(outPos.toInt) = (Run8 | run).toByte
          outPos += 1
        } else {
          run -= 33
          bytes(outPos.toInt) = (Run16 | (run >> 8)).toByte
          outPos += 1
          bytes(outPos.toInt) = (run & 0xff).toByte
          outPos += 1
        }
        run = 0
        runReset = true
      }
      RunUpdate(runReset, run, outPos)
    } ensuring { res =>
      rangesInv(index.length, bytes.length, res.run, res.outPos, li.pxPos) &&&
      (res.reset ==> (res.run == 0 && res.outPos <= outPos0 + 2)) &&&
      (!res.reset ==> (res.outPos == outPos0)) &&&
      ((li.px != li.pxPrev && run0 == 0) ==> (res.run == 0)) &&&
      ((li.px == li.pxPrev && !res.reset) ==> (res.run == run0 + 1)) &&&
      0 <= res.run && res.run < 0x2020
    }

    @opaque
    @inlineOnce
    def mainBody(index: Array[Pixel], bytes: Array[Byte], run1: Long, outPos1: Long)(using li: LoopIter): Long = {
      require(rangesInv(index.length, bytes.length, run1, outPos1, li.pxPos))
      require(li.pxPos + chan <= pixels.length)
      require(positionsIneqInv(run1, outPos1, li.pxPos))
      require((chan == 3) ==> (li.px.a == li.pxPrev.a))
      import li._

      withinBoundsLemma(index.length, bytes.length, run1, outPos1, pxPos)
      assert(outPos1 + run1 * chan + Padding <= maxSize)
      assert(outPos1 + Padding <= maxSize)

      val indexPos = colorPos(px)
      var newOutPos = outPos1

      if (index(indexPos) == px) {
        bytes(newOutPos.toInt) = (Index | indexPos).toByte
        newOutPos += 1
      } else {
        index(indexPos) = px
        val vr = (px.r.toInt & 0xff) - (pxPrev.r.toInt & 0xff)
        val vg = (px.g.toInt & 0xff) - (pxPrev.g.toInt & 0xff)
        val vb = (px.b.toInt & 0xff) - (pxPrev.b.toInt & 0xff)
        val va = (px.a.toInt & 0xff) - (pxPrev.a.toInt & 0xff)

        if (vr > -16 && vr < 17 && vg > -16 && vg < 17 &&
          vb > -16 && vb < 17 && va > -16 && va < 17) {
          if (va == 0 && vr > -2 && vr < 3 && vg > -2 && vg < 3 && vb > -2 && vb < 3) {
            bytes(newOutPos.toInt) = (Diff8 | ((vr + 1) << 4) | (vg + 1) << 2 | (vb + 1)).toByte
            newOutPos += 1
          }
          else if (va == 0 && vr > -16 && vr < 17 && vg > -8 && vg < 9 && vb > -8 && vb < 9) {
            bytes(newOutPos.toInt) = (Diff16 | (vr + 15)).toByte
            newOutPos += 1
            bytes(newOutPos.toInt) = (((vg + 7) << 4) | (vb + 7)).toByte
            newOutPos += 1
          }
          else {
            bytes(newOutPos.toInt) = (Diff24 | ((vr + 15) >> 1)).toByte
            newOutPos += 1
            bytes(newOutPos.toInt) = (((vr + 15) << 7) | ((vg + 15) << 2) | ((vb + 15) >> 3)).toByte
            newOutPos += 1
            bytes(newOutPos.toInt) = (((vb + 15) << 5) | (va + 15)).toByte
            newOutPos += 1
          }
        } else {
          bytes(newOutPos.toInt) = (Color |
            (if (vr != 0) 8 else 0) |
            (if (vg != 0) 4 else 0) |
            (if (vb != 0) 2 else 0) |
            (if (va != 0) 1 else 0)).toByte
          newOutPos += 1
          if (vr != 0) {
            bytes(newOutPos.toInt) = px.r
            newOutPos += 1
          }
          if (vg != 0) {
            bytes(newOutPos.toInt) = px.g
            newOutPos += 1
          }
          if (vb != 0) {
            bytes(newOutPos.toInt) = px.b
            newOutPos += 1
          }
          if (va != 0) {
            bytes(newOutPos.toInt) = px.a
            newOutPos += 1
          }
        }
      }
      assert(newOutPos <= outPos1 + chan + 1)
      positionsIneqIncrementedLemma(index.length, bytes.length, run1, outPos1, pxPos)
      assert(positionsIneqInv(run1, outPos1 + chan + 1, pxPos + chan))
      loopInvUpperOutPosLemma(index.length, bytes.length, run1, outPos1, li.pxPos + chan, newOutPos)
      check(rangesInv(index.length, bytes.length, run1, newOutPos, li.pxPos))
      check(positionsIneqInv(run1, newOutPos, li.pxPos + chan))
      newOutPos
    } ensuring { newOutPos =>
      rangesInv(index.length, bytes.length, run1, newOutPos, li.pxPos) &&
      positionsIneqInv(run1, newOutPos, li.pxPos + chan)
    }

    //////////////////////////////////////////////////////////////////////////////////

    val bytes = Array.fill(maxSize.toInt)(0: Byte)
    val index = Array.fill(64)(Pixel.fromInt(0))
    write32(bytes, 0, MagicNumber)
    write16(bytes, 4, w.toShort)
    write16(bytes, 6, h.toShort)
    write32(bytes, 8, 0)
    val outPos = loop(index, bytes, Pixel.fromRgba(0, 0, 0, 255.toByte), 0, HeaderSize, 0)
    val dataLen = outPos + Padding - HeaderSize
    write32(bytes, 8, dataLen.toInt)
  }

  sealed trait OptionMut[@mutable T]
  case class SomeMut[@mutable T](v: T) extends OptionMut[T]
  case class NoneMut[@mutable T]() extends OptionMut[T]

  def decode(bytes: Array[Byte], chan: Int): OptionMut[(Array[Byte], Int, Int)] = {
    require(3 <= chan && chan <= 4)
    require(bytes.length >= HeaderSize)
    val magic = read32(bytes, 0)
    val w = read16(bytes, 4).toInt
    val h = read16(bytes, 6).toInt
    val dataLen = read32(bytes, 8)

    if (0 < w && w < 8192 && 0 < h && h < 8192 && magic == MagicNumber && bytes.length == dataLen + HeaderSize) {
      val pixels = doDecode(bytes, chan, w, h)
      SomeMut((pixels, w, h))
    } else {
      NoneMut()
    }
  }

  def doDecode(bytes: Array[Byte], chan: Int, w: Int, h: Int): Array[Byte] = {
    require(3 <= chan && chan <= 4)
    require(bytes.length >= HeaderSize)
    require(0 < w && w < 8192 && 0 < h && h < 8192)

    val chunksLen = bytes.length - Padding

    def rangesInv(indexLen: Int, pixelsLen: Int, run: Int, inPos: Int, pxPos: Int): Boolean =
      0 <= pxPos && pxPos <= pixelsLen &&
        ((pxPos % chan) == 0) &&
        w * h * chan == pixelsLen &&
        pixelsLen % chan == 0 &&
        0 <= run && run < 0x2020 &&
        HeaderSize <= inPos && inPos <= bytes.length &&
        indexLen == 64

    @opaque
    def loop(index: Array[Pixel], pixels: Array[Byte], px0: Pixel, run0: Int, inPos0: Int, pxPos: Int): Unit = {
      require(rangesInv(index.length, pixels.length, run0, inPos0, pxPos))
      require(pxPos < pixels.length)

      var px = px0
      var run = run0
      var inPos = inPos0

      if (run > 0) {
        run -= 1
      } else if (inPos < chunksLen) {
        val b1 = bytes(inPos).toInt & 0xff
        inPos += 1

        if ((b1 & Mask2) == Index) {
          px = index((b1 ^ Index) & 0xff)
        } else if ((b1 & Mask3) == Run8) {
          run = b1 & 0x1f
        } else if ((b1 & Mask3) == Run16) {
          val b2 = bytes(inPos).toInt & 0xff
          inPos += 1
          run = (((((b1 & 0x1f) << 8) & 0xffff) | (b2 & 0xff)) & 0xffff) + 32
        } else if ((b1 & Mask2) == Diff8) {
          px = px.incremented(
            (((b1 >> 4) & 0x03) - 1).toByte,
            (((b1 >> 2) & 0x03) - 1).toByte,
            ((b1 & 0x03) - 1).toByte)
        } else if ((b1 & Mask3) == Diff16) {
          val b2 = bytes(inPos).toInt & 0xff
          inPos += 1
          px = px.incremented(
            ((b1 & 0x1f) - 15).toByte,
            (((b2 >> 4) & 0xff) - 7).toByte,
            ((b2 & 0x0f) - 7).toByte)
        } else if ((b1 & Mask4) == Diff24) {
          val b2 = bytes(inPos).toInt & 0xff
          inPos += 1
          val b3 = bytes(inPos).toInt & 0xff
          inPos += 1
          px = px.incremented(
            (((
              (((b1 & 0x0f) << 1) & 0xff) |
                ((b2 >> 7) & 0xff)
              ) & 0xff) - 15).toByte,
            ((((b2 & 0x7c) >> 2) & 0xff) - 15).toByte,
            (((
              (((b2 & 0x03) << 3) & 0xff) |
                (((b3 & 0xe0) >> 5) & 0xff)
              ) & 0xff) - 15).toByte,
            ((b3 & 0x1f) - 15).toByte
          )
        } else if ((b1 & Mask4) == Color) {
          if ((b1 & 8) != 0) {
            px = px.withRgba(r = bytes(inPos))
            inPos += 1
          }
          if ((b1 & 4) != 0) {
            px = px.withRgba(g = bytes(inPos))
            inPos += 1
          }
          if ((b1 & 2) != 0) {
            px = px.withRgba(b = bytes(inPos))
            inPos += 1
          }
          if ((b1 & 1) != 0) {
            px = px.withRgba(a = bytes(inPos))
            inPos += 1
          }
        }

        index(colorPos(px)) = px
      }

      assert((pxPos % chan) == 0)
      assert(w * h * chan == pixels.length)
      assert((pixels.length % chan) == 0)
      assert(pxPos + chan <= pixels.length)
      pixels(pxPos) = px.r
      pixels(pxPos + 1) = px.g
      pixels(pxPos + 2) = px.b
      if (chan == 4) {
        pixels(pxPos + 3) = px.a
      }

      if (pxPos + chan < pixels.length) {
        loop(index, pixels, px, run, inPos, pxPos + chan)
      } else ()
    }

    val pixels = Array.fill(w * h * chan)(0: Byte)
    val index = Array.fill(64)(Pixel.fromInt(0))
    loop(index, pixels, Pixel.fromRgba(0, 0, 0, 255.toByte), 0, HeaderSize, 0)
    pixels
  }
}
