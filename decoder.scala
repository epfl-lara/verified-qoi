import stainless.*
import stainless.lang.{inline as inlineCall, *}
import stainless.collection.*
import stainless.annotation.{induct, inlineOnce, mutable, opaque, pure}
import stainless.proof.*
import common.*

object decoder {

  sealed trait OptionMut[@mutable T]
  case class SomeMut[@mutable T](v: T) extends OptionMut[T]
  case class NoneMut[@mutable T]() extends OptionMut[T]

  case class Ctx(bytes: Array[Byte], w: Long, h: Long, chan: Long) {
    require(w > 0 && h > 0 && w < 8192 && h < 8192 &&
      3 <= chan && chan <= 4 &&
      HeaderSize <= bytes.length)

    @inline
    def pixelsLen: Long = {
      w * h * chan
    }.ensuring(_ % chan == 0)

    @inline
    def chunksLen: Long = bytes.length - Padding
  }

  /////////////////////////////////////////////////////////////////////////////////////////////////////

  def runInv(run: Long): Boolean =
    0 <= run && run <= 62

  def pxPosInv(pxPos: Long)(using Ctx): Boolean =
    0 <= pxPos && pxPos <= pixelsLen && pxPos % chan == 0

  def inPosInv(inPos: Long)(using Ctx): Boolean =
    HeaderSize <= inPos && inPos <= bytes.length - Padding

  def rangesInv(run: Long, inPos: Long, pxPos: Long)(using Ctx): Boolean =
    pxPosInv(pxPos) && runInv(run) && inPosInv(inPos)

  def rangesInv(indexLen: Long, run: Long, inPos: Long, pxPos: Long)(using Ctx): Boolean =
    pxPosInv(pxPos) && runInv(run) && inPosInv(inPos) && indexLen == 64

  /////////////////////////////////////////////////////////////////////////////////////////////////////

  def decodeDiff(pxPrev: Int, b1: Int): Int = {
    require((b1 & Mask2) == OpDiff)
    Pixel.incremented(pxPrev)(
      (((b1 >> 4) & 0x03) - 2).toByte,
      (((b1 >> 2) & 0x03) - 2).toByte,
      ((b1 & 0x03) - 2).toByte)
  }

  def decodeLuma(pxPrev: Int, b1: Int, b2: Int): Int = {
    require((b1 & Mask2) == OpLuma)
    val vg = (b1 & 0x3f) - 32
    Pixel.incremented(pxPrev)(
      (vg - 8 + ((b2 >> 4) & 0x0f)).toByte,
      vg.toByte,
      (vg - 8 + (b2 & 0x0f)).toByte)
  }

  def decodeRun(b1: Int): Int = {
    require((b1 & Mask2) == OpRun)
    b1 & 0x3f
  }

  @pure
  @opaque
  @inlineOnce
  def decodeBigStepPropLemma(pixels: Array[Byte],
                             pxPrev: Int, pxPos0: Long,
                             px2: Int, pxPos2: Long)(using Ctx): Unit = {
    require(0 <= pxPos0 && pxPos0 < pxPos2 && pxPos2 <= pixels.length)
    require(pxPos0 + chan < pxPos2)
    require(pxPos0 % chan == 0 && pxPos2 % chan == 0)
    require(pixels.length % chan == 0)
    require(samePixels(pixels, pxPrev, pxPos0, chan))
    require {
      sorry((pxPos0 + chan) % chan == 0) // TODO
      decodeBigStepProp(pixels, pxPrev, pxPos0 + chan, px2, pxPos2)
    }
  }.ensuring(_ => decodeBigStepProp(pixels, pxPrev, pxPos0, px2, pxPos2))

  @pure
  def decodeBigStepProp(pixels: Array[Byte],
                        pxPrev: Int, pxPos0: Long,
                        px2: Int, pxPos2: Long)(using Ctx): Boolean = {
    require(0 <= pxPos0 && pxPos0 < pxPos2 && pxPos2 <= pixels.length)
    require(pxPos0 % chan == 0 && pxPos2 % chan == 0)
    require(pixels.length % chan == 0)
    assert(chan <= pxPos2)
    sorry((pxPos2 - chan) % chan == 0) // TODO

    ((pxPos0 + 2 * chan <= pxPos2) ==> samePixelsForall(pixels, pxPrev, pxPos0, pxPos2 - chan, chan)) &&
    samePixels(pixels, px2, pxPos2 - chan, chan)
  }

  enum DecodedNext {
    case Run(run: Long)
    case DiffIndexColor(px: Int)
  }
  import DecodedNext._

  // TODO: Pas opaque, on a besoin de voir ce qu'il y a dedans pour writePixelPureBytesEqLemma
  // OK
//  @opaque
//  @inlineOnce
  def writePixel(pixels: Array[Byte], px: Int, pxPos: Long)(using Ctx): Unit = {
    require(pixels.length == pixelsLen)
    require(pxPosInv(pxPos))
    require(pxPos + chan <= pixels.length)

    val pixelsPre = freshCopy(pixels)
    eqImpliesArraysEq(pixelsPre, pixels, 0, pxPos)
    assert(arraysEq(pixelsPre, pixels, 0, pxPos))

    pixels(pxPos.toInt) = Pixel.r(px)
    updatedAtArraysEq(pixelsPre, pxPos, Pixel.r(px))
    assert(arraysEq(pixelsPre, pixels, 0, pxPos))
    val pixelsR = freshCopy(pixels)

    pixels(pxPos.toInt + 1) = Pixel.g(px)
    updatedAtArraysEq(pixelsR, pxPos + 1, Pixel.g(px))
    arraysEqDropRightLemma(pixelsR, pixels, 0, pxPos, pxPos + 1)
    assert(arraysEq(pixelsR, pixels, 0, pxPos))
    val pixelsRG = freshCopy(pixels)

    pixels(pxPos.toInt + 2) = Pixel.b(px)
    updatedAtArraysEq(pixelsRG, pxPos + 2, Pixel.b(px))
    arraysEqDropRightLemma(pixelsRG, pixels, 0, pxPos, pxPos + 2)
    assert(arraysEq(pixelsRG, pixels, 0, pxPos))
    val pixelsRGB = freshCopy(pixels)

    arraysEqTransLemma(pixelsPre, pixelsR, pixelsRG, 0, pxPos)
    arraysEqTransLemma(pixelsPre, pixelsRG, pixelsRGB, 0, pxPos)
    assert(arraysEq(pixelsPre, pixelsRGB, 0, pxPos))

    if (chan == 4) {
      pixels(pxPos.toInt + 3) = Pixel.a(px)
      updatedAtArraysEq(pixelsRGB, pxPos + 3, Pixel.a(px))
      arraysEqDropRightLemma(pixelsRGB, pixels, 0, pxPos, pxPos + 3)
      assert(arraysEq(pixelsRGB, pixels, 0, pxPos))
      arraysEqTransLemma(pixelsPre, pixelsRGB, pixels, 0, pxPos)
      assert(arraysEq(pixelsPre, pixels, 0, pxPos))
    } else {
      assert(pixelsRGB == pixels)
      check(arraysEq(pixelsPre, pixels, 0, pxPos))
    }
  }.ensuring { _ =>
    old(pixels).length == pixels.length &&&
    arraysEq(old(pixels), pixels, 0, pxPos) &&&
    samePixels(pixels, px, pxPos, chan)
  }

  // OK
  @pure
  def writePixelPure(pixels: Array[Byte], px: Int, pxPos: Long)(using Ctx): Array[Byte] = {
    require(pixels.length == pixelsLen)
    require(pxPosInv(pxPos))
    require(pxPos + chan <= pixels.length)
    val pixelsCpy = freshCopy(pixels)
    writePixel(pixelsCpy, px, pxPos)
    pixelsCpy
  }.ensuring { newPixels =>
    pixels.length == newPixels.length &&&
    arraysEq(pixels, newPixels, 0, pxPos) &&&
    samePixels(newPixels, px, pxPos, chan)
  }

  // OK
  @pure
  @opaque
  @inlineOnce
  def writePixelPureBytesEqLemma(pixels: Array[Byte], px: Int, pxPos: Long, from: Long, to: Long, bytes2: Array[Byte])(using ctx1: Ctx): Unit = {
    require(pixels.length == pixelsLen)
    require(pxPosInv(pxPos))
    require(pxPos + chan <= pixels.length)
    require(bytes.length == bytes2.length)
    require(0 <= from && from <= to && to <= bytes.length)
    require(arraysEq(bytes, bytes2, from, to))

    val ctx2 = Ctx(freshCopy(bytes2), w, h, chan)
    val pix1 = writePixelPure(pixels, px, pxPos)(using ctx1)
    val pix2 = writePixelPure(pixels, px, pxPos)(using ctx2)

    {
      ()
    }.ensuring(_ => pix1 == pix2)
  }

  @opaque
  @inlineOnce
  def writeRunPixels(pixels: Array[Byte], px: Int, run0: Long, pxPos0: Long)(using Ctx): (Long, Long) = {
    require(pixels.length == pixelsLen)
    require(runInv(run0))
    require(pxPosInv(pxPos0))
    require(pxPos0 + chan <= pixels.length)

    // Note: un run de 0 est possible: cela signifie que l'on répète 1 fois le px précédent

    val pxPos0PlusChan = pxPos0 + chan
    modSumLemma(pxPos0, chan)
    assert(pxPos0PlusChan % chan == 0)

    val pixelsPre = freshCopy(pixels)

    writePixel(pixels, px, pxPos0)

    assert(pixels.length == pixelsPre.length)
    assert(arraysEq(pixelsPre, pixels, 0, pxPos0))

    assert(samePixels(pixels, px, pxPos0, chan))
    samePixelsSingleElementRange(pixels, px, pxPos0, chan)
    check(samePixelsForall(pixels, px, pxPos0, pxPos0PlusChan, chan))

    if (run0 > 0 && pxPos0 + chan < pixels.length) {
      modLeqLemma(pxPos0PlusChan, pixels.length, chan)
      assert(pxPos0PlusChan + chan <= pixels.length)

      val run0Minus1 = run0 - 1

      val pixelsPreRec = freshCopy(pixels)
      eqImpliesArraysEq(pixelsPreRec, pixels, 0, pxPos0)
      assert(arraysEq(pixelsPreRec, pixels, 0, pxPos0))
      assert(arraysEq(pixelsPre, pixelsPreRec, 0, pxPos0))
      assert(samePixelsForall(pixelsPreRec, px, pxPos0, pxPos0PlusChan, chan))

      val (run2, pxPos2) = writeRunPixels(pixels, px, run0Minus1, pxPos0PlusChan)
      assert(pixels.length == pixelsPre.length)
      assert(pxPos0PlusChan < pxPos2)
      assert(arraysEq(pixelsPreRec, pixels, 0, pxPos0PlusChan))
      assert(samePixelsForall(pixels, px, pxPos0PlusChan, pxPos2, chan))

      // 2.
      arraysEqDropRightLemma(pixelsPreRec, pixels, 0, pxPos0, pxPos0PlusChan)
      assert(arraysEq(pixelsPreRec, pixels, 0, pxPos0))
      arraysEqTransLemma(pixelsPre, pixelsPreRec, pixels, 0, pxPos0)
      check(arraysEq(pixelsPre, pixels, 0, pxPos0))

      // 3.
      arraysEqDropLeftLemma(pixelsPreRec, pixels, 0, pxPos0, pxPos0PlusChan)
      assert(arraysEq(pixelsPreRec, pixels, pxPos0, pxPos0PlusChan))
      samePixelsForallUnchangedLemma(pixelsPreRec, pixels, px, pxPos0, pxPos0PlusChan, chan)
      assert(samePixelsForall(pixels, px, pxPos0, pxPos0PlusChan, chan))
      samePixelsForallCombinedLemma(pixels, px, pxPos0, pxPos0PlusChan, pxPos2, chan)
      check(samePixelsForall(pixels, px, pxPos0, pxPos2, chan))

      // 4.
      assert(pxPos0 + chan < pxPos2)
      check(pxPos0 < pxPos2)

      // 7.
      assert((pxPos0PlusChan + chan + run0Minus1 * chan <= pixels.length) ==> (run2 == 0 && pxPos2 == pxPos0PlusChan + chan * (run0Minus1 + 1)))
      assert(((pxPos0 + chan + chan + (run0 - 1) * chan <= pixels.length) ==> (run2 == 0 && pxPos2 == pxPos0 + chan + chan * run0))
        because (run0Minus1 == run0 - 1 && pxPos0PlusChan == pxPos0 + chan))
      assert((run0 - 1) * chan == run0 * chan - chan)
      assert((pxPos0 + chan + chan) + ((run0 - 1) * chan) == (pxPos0 + chan + chan) + (run0 * chan - chan))
      assert(pxPos0 + chan + chan + run0 * chan - chan == pxPos0 + chan + run0 * chan)
      assert(pxPos0 + chan + chan + (run0 - 1) * chan == pxPos0 + chan + run0 * chan)
      assert(pxPos0 + chan + chan * run0 == pxPos0 + chan * (run0 + 1))
      check((pxPos0 + chan + run0 * chan <= pixels.length) ==> (run2 == 0 && pxPos2 == pxPos0 + chan * (run0 + 1))) // TODO: Timeout

      (run2, pxPos2)
    } else {
      (run0, pxPos0 + chan)
    }
  }.ensuring { case (run2, pxPos2) =>
    old(pixels).length == pixels.length &&&
    arraysEq(old(pixels), pixels, 0, pxPos0) &&&
    samePixelsForall(pixels, px, pxPos0, pxPos2, chan) &&&
    pxPos0 < pxPos2 &&&
    pxPos2 <= pixels.length &&&
    pxPos2 % chan == 0 &&&
    ((pxPos0 + chan + chan * run0 <= pixels.length) ==> (run2 == 0 && pxPos2 == pxPos0 + chan * (run0 + 1)))
  }

  case class DecodingIteration(px: Int, inPos: Long, pxPos: Long, remainingRun: Long)

  def decodeNext(index: Array[Int], pixels: Array[Byte], pxPrev: Int, inPos0: Long, pxPos0: Long)(using Ctx): (DecodedNext, DecodingIteration) = {
    require(index.length == 64)
    require(pixels.length == pixelsLen)
    require(inPosInv(inPos0))
    require(pxPosInv(pxPos0))
    require(pxPos0 + chan <= pixels.length)
    require(inPos0 < chunksLen)

    val pixelsPre = freshCopy(pixels)
    val indexPre = freshCopy(index)
    val (decRes, inPos) = doDecodeNext(index, pxPrev, inPos0)

    decRes match {
      case Run(run) =>
        val (resRun, resPxPos) = writeRunPixels(pixels, pxPrev, run, pxPos0)
        check(pxPos0 < resPxPos && resPxPos <= pixels.length && resPxPos % chan == 0)
        check(pixelsPre.length == pixels.length)
        check(arraysEq(pixelsPre, pixels, 0, pxPos0))
        check(samePixelsForall(pixels, pxPrev, pxPos0, resPxPos, chan))
        check((pxPos0 + chan + chan * run <= pixels.length) ==> (resRun == 0 && resPxPos == pxPos0 + chan * (run + 1)))
        (decRes, DecodingIteration(pxPrev, inPos, resPxPos, resRun))

      case DiffIndexColor(px) =>
        writePixel(pixels, px, pxPos0)
        index(colorPos(px)) = px
        check(pixelsPre.length == pixels.length)
        check(arraysEq(pixelsPre, pixels, 0, pxPos0))
        check(indexPre.updated(colorPos(px), px) == index)
        check(samePixels(pixels, px, pxPos0, chan))
        (decRes, DecodingIteration(px, inPos, pxPos0 + chan, 0))
    }
  }

  @pure
  def decodeNextPure(index: Array[Int], pixels: Array[Byte], pxPrev: Int, inPos0: Long, pxPos0: Long)(using Ctx): (Array[Int], Array[Byte], DecodedNext, DecodingIteration) = {
    require(index.length == 64)
    require(pixels.length == pixelsLen)
    require(inPosInv(inPos0))
    require(pxPosInv(pxPos0))
    require(pxPos0 + chan <= pixels.length)
    require(inPos0 < chunksLen)

    val indexPre = freshCopy(index)
    val pixelsPre = freshCopy(pixels)
    val (decRes, decIter) = decodeNext(indexPre, pixelsPre, pxPrev, inPos0, pxPos0)
    (indexPre, pixelsPre, decRes, decIter)
  }.ensuring {
    case (indexPre, pixelsPre, _, decIter) =>
      indexPre.length == 64 &&&
      pixelsPre.length == pixels.length &&&
      0 <= decIter.inPos &&&
      inPos0 < decIter.inPos &&&
      decIter.pxPos % chan == 0
  }

  def decodeRange(index: Array[Int], pixels: Array[Byte], pxPrev: Int,
                  inPos0: Long, untilInPos: Long, pxPos0: Long)(using Ctx): DecodingIteration = {
    decreases(untilInPos - inPos0)
    require(index.length == 64)
    require(pixels.length == pixelsLen)
    require(inPosInv(inPos0))
    require(pxPosInv(pxPos0))
    require(pxPos0 + chan <= pixels.length)
    require(inPos0 < untilInPos && untilInPos <= chunksLen)

    val indexPre = freshCopy(index)
    val pixelsPre = freshCopy(pixels)
    val (res, decIter) = decodeNext(index, pixels, pxPrev, inPos0, pxPos0)
    check(decIter.pxPos % chan == 0)
    // TODO: Si on atteint la fin de chunksLen, il faut remplir le reste avec pxPrev!!!!!
    if (decIter.inPos < untilInPos && decIter.pxPos + chan <= pixels.length) {
      decodeRange(index, pixels, decIter.px, decIter.inPos, untilInPos, decIter.pxPos)
    } else {
      decIter
    }
    /*match {
      case (Run(r), decIter) =>
        ???
      case (DiffIndexColor(px), decIter) =>
        decodeRange(index, pixels, px, decIter.inPos, untilInPos, decIter.pxPos)
    }*/
  }.ensuring { decIter =>
    index.length == 64 &&&
    old(pixels).length == pixels.length &&&
    pxPosInv(decIter.pxPos) &&&
    HeaderSize <= decIter.inPos /*&&&
    (!(decIter.inPos < untilInPos && decIter.pxPos + chan <= pixels.length) ==>
      (old(index).updated(colorPos(decIter.px), decIter.px) == index))*/
    // &&& // && decIter.inPos <= bytes.length
    // decodeRangePureMergedForall(index, old(pixels), pxPrev, inPos0, untilInPos, pxPos0)
  }

  @opaque
  @inlineOnce
  @pure
  def decodeRangePureLemma(index: Array[Int], pixels: Array[Byte], pxPrev: Int,
                           inPos0: Long, untilInPos: Long, pxPos0: Long)(using Ctx): (Array[Int], Array[Byte], DecodingIteration) = {
    require(index.length == 64)
    require(pixels.length == pixelsLen)
    require(inPosInv(inPos0))
    require(pxPosInv(pxPos0))
    require(pxPos0 + chan <= pixels.length)
    require(inPos0 < untilInPos && untilInPos <= chunksLen)

    val indexCpy = freshCopy(index)
    val pixelsCpy = freshCopy(pixels)
    val res = decodeRange(indexCpy, pixelsCpy, pxPrev, inPos0, untilInPos, pxPos0)
    (indexCpy, pixelsCpy, res)
  }.ensuring { case (indexCpy, pixelsCpy, res) =>
    0 <= res.pxPos &&& res.pxPos <= pixels.length &&&
    res.pxPos % chan == 0
    indexCpy.length == 64 &&&
    pixelsCpy.length == pixels.length
  }

  @opaque
  @inlineOnce
  @pure
  def decodeRangePureNextLemma(index: Array[Int],
                               pixels: Array[Byte],
                               pxPrev: Int,
                               inPos0: Long,
                               inPos1: Long,
                               pxPos0: Long)(using Ctx): Unit = {
    require(index.length == 64)
    require(pixels.length == pixelsLen)
    require(inPosInv(inPos0))
    require(pxPosInv(pxPos0))
    require(pxPos0 + chan <= pixels.length)
    require(inPos0 < inPos1 && inPos1 <= chunksLen)

    val (index1, pixels1, decIter1) = decodeRangePureLemma(index, pixels, pxPrev, inPos0, inPos1, pxPos0)
    val (indexNext, pixelNext, _, decIterNext) = decodeNextPure(index, pixels, pxPrev, inPos0, pxPos0)
    require(decIterNext.inPos < inPos1 && decIterNext.pxPos < pixels.length && decIterNext.pxPos + chan <= pixels.length)
    val (index2, pixels2, decIter2) = decodeRangePureLemma(indexNext, pixelNext, decIterNext.px, decIterNext.inPos, inPos1, decIterNext.pxPos)

    {
      ()
    }.ensuring { _ =>
      decIter1 == decIter2 &&&
      index1 == index2 &&&
      pixels1 == pixels2
    }
  }

  @opaque
  @inlineOnce
  @pure
  def decodeRangePureBytesEqLemma(index: Array[Int],
                                  pixels: Array[Byte],
                                  pxPrev: Int,
                                  inPos0: Long,
                                  untilInPos: Long,
                                  pxPos0: Long,
                                  bytes2: Array[Byte])(using ctx1: Ctx): Unit = {
    decreases(untilInPos - inPos0)
    require(index.length == 64)
    require(pixels.length == pixelsLen)
    require(inPosInv(inPos0))
    require(pxPosInv(pxPos0))
    require(pxPos0 + chan <= pixels.length)
    require(inPos0 < untilInPos && untilInPos <= chunksLen)
    require(bytes.length == bytes2.length)
    require(arraysEq(bytes, bytes2, inPos0, untilInPos))

    val ctx2 = Ctx(freshCopy(bytes2), w, h, chan)
    val (ix1, pix1, decIter1) = decodeRangePureLemma(index, pixels, pxPrev, inPos0, untilInPos, pxPos0)(using ctx1)
    require(decIter1.pxPos < pixels.length && decIter1.pxPos + chan <= pixels.length)
    require(decIter1.inPos == untilInPos)
    val (ix2, pix2, decIter2) = decodeRangePureLemma(index, pixels, pxPrev, inPos0, untilInPos, pxPos0)(using ctx2)
//    require(decIter2.pxPos < pixels.length && decIter2.pxPos + chan <= pixels.length)
//    require(decIter2.inPos == untilInPos)

    {
      assert(ctx2.bytes == bytes2)
      val (ix1Next, pix1Next, _, decIter1Next) = decodeNextPure(index, pixels, pxPrev, inPos0, pxPos0)(using ctx1)
      val (ix2Next, pix2Next, _, decIter2Next) = decodeNextPure(index, pixels, pxPrev, inPos0, pxPos0)(using ctx2)

      assert(inPos0 < decIter1Next.inPos)
      assert(decIter1Next.inPos <= decIter1.inPos)
      arraysEqDropRightLemma(bytes, bytes2, inPos0, decIter1Next.inPos, untilInPos)
      assert(arraysEq(bytes, bytes2, inPos0, decIter1Next.inPos))
      decodeNextPureBytesEqLemma(index, pixels, pxPrev, inPos0, pxPos0, bytes2)
      assert(decIter1Next == decIter2Next)
      assert(ix1Next == ix2Next)
      assert(pix1Next == pix2Next)

      if (decIter1Next.inPos == decIter1.inPos) {
        assert(decIter1Next.inPos == untilInPos)
        assert(ix1Next == ix1)
        assert(pix1Next == pix1)
        assert(decIter1Next == decIter1)
        check(ix1 == ix2)
        check(pix1 == pix2)
        check(decIter1 == decIter2)
      } else {
        assert(0 <= decIter1Next.inPos && decIter1Next.inPos < decIter1.inPos)
        assert(ix1Next.length == 64 && pixels.length == pix1Next.length)
        assert(decIter1Next.pxPos < pixels.length)
        assert(decIter1Next.pxPos + chan <= pixels.length)

        arraysEqDropLeftLemma(bytes, bytes2, inPos0, decIter1Next.inPos, untilInPos)
        assert(arraysEq(bytes, bytes2, decIter1Next.inPos, untilInPos))
        decodeRangePureBytesEqLemma(ix1Next, pix1Next, decIter1Next.px, decIter1Next.inPos, untilInPos, decIter1Next.pxPos, bytes2)
        val (ix1Rec, pix1Rec, decIter1Rec) = decodeRangePureLemma(ix1Next, pix1Next, decIter1Next.px, decIter1Next.inPos, untilInPos, decIter1Next.pxPos)(using ctx1)
        val (ix2Rec, pix2Rec, decIter2Rec) = decodeRangePureLemma(ix1Next, pix1Next, decIter1Next.px, decIter1Next.inPos, untilInPos, decIter1Next.pxPos)(using ctx2)
        assert(ix1Rec == ix2Rec)
        assert(pix1Rec == pix2Rec)
        assert(decIter1Rec == decIter2Rec)

        decodeRangePureNextLemma(index, pixels, pxPrev, inPos0, untilInPos, pxPos0)
        assert(ix1 == ix1Rec)
        assert(pix1 == pix1Rec)
        assert(decIter1 == decIter1Rec)

        check(ix1 == ix2)
        check(pix1 == pix2)
        check(decIter1 == decIter2)
      }
    }.ensuring { _ =>
      ix1 == ix2 &&&
      pix1 == pix2 &&&
      decIter1 == decIter2
    }
  }

  @opaque
  @inlineOnce
  @pure
  def decodeRangePureMergedLemma(index: Array[Int],
                                 pixels: Array[Byte],
                                 pxPrev: Int,
                                 inPos0: Long,
                                 inPos1: Long,
                                 inPos2: Long,
                                 pxPos0: Long)(using Ctx): Unit = {
    decreases(inPos2 - inPos0)
    require(index.length == 64)
    require(pixels.length == pixelsLen)
    require(inPosInv(inPos0))
    require(pxPosInv(pxPos0))
    require(pxPos0 + chan <= pixels.length)
    require(inPos0 < inPos1 && inPos1 < inPos2 && inPos2 <= chunksLen)
    val (index1, pixels1, decIter1) = decodeRangePureLemma(index, pixels, pxPrev, inPos0, inPos1, pxPos0)
    require(decIter1.pxPos < pixels.length && decIter1.pxPos + chan <= pixels.length)
    require(decIter1.inPos == inPos1)
    val (index2, pixels2, decIter2) = decodeRangePureLemma(index1, pixels1, decIter1.px, inPos1, inPos2, decIter1.pxPos)
    val (index3, pixels3, decIter3) = decodeRangePureLemma(index, pixels, pxPrev, inPos0, inPos2, pxPos0)

    {
      val (indexNext, pixelNext, _, decIterNext) = decodeNextPure(index, pixels, pxPrev, inPos0, pxPos0)
      if (decIterNext.inPos == decIter1.inPos) {
        check(decIter2.inPos == decIter3.inPos)
        check(decIter2.pxPos == decIter3.pxPos)
      } else {
        assert(0 <= decIterNext.inPos && decIterNext.inPos < decIter1.inPos)
        assert(indexNext.length == 64 && pixels.length == pixelNext.length)
        assert(decIterNext.pxPos < pixels.length)
        assert(decIterNext.pxPos + chan <= pixels.length)

        val (index1Rec, pixels1Rec, decIter1Rec) = decodeRangePureLemma(indexNext, pixelNext, decIterNext.px, decIterNext.inPos, inPos1, decIterNext.pxPos)
        decodeRangePureNextLemma(index, pixels, pxPrev, inPos0, inPos1, pxPos0)
        assert(decIter1Rec == decIter1)
        assert(index1Rec == index1)
        assert(pixels1Rec == pixels1)

        val (index2Rec, pixels2Rec, decIter2Rec) = decodeRangePureLemma(index1Rec, pixels1Rec, decIter1Rec.px, inPos1, inPos2, decIter1Rec.pxPos)

        val (index3Rec, pixels3Rec, decIter3Rec) = decodeRangePureLemma(indexNext, pixelNext, decIterNext.px, decIterNext.inPos, inPos2, decIterNext.pxPos)

        decodeRangePureMergedLemma(indexNext, pixelNext, decIterNext.px, decIterNext.inPos, inPos1, inPos2, decIterNext.pxPos)
        assert(decIter2Rec == decIter3Rec)

        decodeRangePureNextLemma(index, pixels, pxPrev, inPos0, inPos2, pxPos0)
        assert(decIter3Rec == decIter3)
        assert(index3Rec == index3)
        assert(pixels3Rec == pixels3)

        assert(decodeRangePureLemma(index1Rec, pixels1Rec, decIter1Rec.px, inPos1, inPos2, decIter1Rec.pxPos) ==
          decodeRangePureLemma(index1, pixels1, decIter1.px, inPos1, inPos2, decIter1.pxPos))
        assert(decIter2Rec == decIter2)
        assert(index2Rec == index2)
        assert(pixels2Rec == pixels2)

        check(decIter2 == decIter3)
        assert(index2 == index3)
        assert(pixels2 == pixels3)
      }
    }.ensuring { _ =>
      decIter2 == decIter3 &&&
      index2 == index3 &&&
      pixels2 == pixels3
    }
  }

  // OK
  @pure
  def doDecodeNext(index: Array[Int], pxPrev: Int, inPos0: Long)(using Ctx): (DecodedNext, Long) = {
    require(index.length == 64)
    require(HeaderSize <= inPos0 && inPos0 < chunksLen)
    var px = pxPrev
    var inPos = inPos0
    var run = 0L

    val b1 = bytes(inPos.toInt).toInt & 0xff
    inPos += 1

    if (b1 == OpRgb) {
      val px = Pixel.withRgba(pxPrev)(r = bytes(inPos.toInt), g = bytes(inPos.toInt + 1), b = bytes(inPos.toInt + 2))
      inPos += 3
      (DiffIndexColor(px), inPos)
    } else if (b1 == OpRgba) {
      val px = Pixel.withRgba(pxPrev)(r = bytes(inPos.toInt), g = bytes(inPos.toInt + 1), b = bytes(inPos.toInt + 2), a = bytes(inPos.toInt + 3))
      inPos += 4
      (DiffIndexColor(px), inPos)
    } else if ((b1 & Mask2) == OpIndex) {
      val px = index(b1)
      (DiffIndexColor(px), inPos)
    } else if ((b1 & Mask2) == OpDiff) {
      val px = decodeDiff(pxPrev, b1)
      (DiffIndexColor(px), inPos)
    } else if ((b1 & Mask2) == OpLuma) {
      val b2 = bytes(inPos.toInt).toInt & 0xff
      inPos += 1
      val px = decodeLuma(pxPrev, b1, b2)
      (DiffIndexColor(px), inPos)
    } else if ((b1 & Mask2) == OpRun) {
      val run = decodeRun(b1)
      (Run(run), inPos)
    } else {
      (DiffIndexColor(pxPrev), inPos)
    }
  }.ensuring { case (_, inPos) => inPos <= inPos0 + 5 }

  // TODO
  @opaque
  @inlineOnce
  @pure
  def decodeNextPureBytesEqLemma(index: Array[Int], pixels: Array[Byte], pxPrev: Int, inPos0: Long, pxPos0: Long, bytes2: Array[Byte])(using ctx1: Ctx): Unit = {
    require(index.length == 64)
    require(pixels.length == pixelsLen)
    require(inPosInv(inPos0))
    require(pxPosInv(pxPos0))
    require(pxPos0 + chan <= pixels.length)
    require(inPos0 < chunksLen)
    require(bytes.length == bytes2.length)
    val ctx2 = Ctx(freshCopy(bytes2), w, h, chan)
    val (ix1, pix1, res1, decIter1) = decodeNextPure(index, pixels, pxPrev, inPos0, pxPos0)(using ctx1)
    require(arraysEq(bytes, bytes2, inPos0, decIter1.inPos))
    val (ix2, pix2, res2, decIter2) = decodeNextPure(index, pixels, pxPrev, inPos0, pxPos0)(using ctx2)

    {
      doDecodeNextBytesEqLemma(index, pxPrev, inPos0, bytes2)
      check(res1 == res2)
      check(ix1 == ix2)
      assert(bytes(inPos0.toInt) == bytes2(inPos0.toInt))
      assert(decIter1.inPos <= inPos0 + 5)
      assert((inPos0 + 1 < decIter1.inPos) ==> {
        arraysEqAtIndex(bytes, bytes2, inPos0, decIter1.inPos, inPos0 + 1)
        bytes((inPos0 + 1).toInt) == bytes2((inPos0 + 1).toInt)
      })
      assert((inPos0 + 2 < decIter1.inPos) ==> {
        arraysEqAtIndex(bytes, bytes2, inPos0, decIter1.inPos, inPos0 + 2)
        bytes((inPos0 + 2).toInt) == bytes2((inPos0 + 2).toInt)
      })
      assert((inPos0 + 3 < decIter1.inPos) ==> {
        arraysEqAtIndex(bytes, bytes2, inPos0, decIter1.inPos, inPos0 + 3)
        bytes((inPos0 + 3).toInt) == bytes2((inPos0 + 3).toInt)
      })
      assert((inPos0 + 4 < decIter1.inPos) ==> {
        arraysEqAtIndex(bytes, bytes2, inPos0, decIter1.inPos, inPos0 + 4)
        bytes((inPos0 + 4).toInt) == bytes2((inPos0 + 4).toInt)
      })
      val b1 = bytes(inPos0.toInt).toInt & 0xff
      if (b1 == OpRgb) {
        assert(decIter1.inPos == inPos0 + 4)
        assert(bytes((inPos0 + 1).toInt) == bytes2((inPos0 + 1).toInt))
        assert(bytes((inPos0 + 2).toInt) == bytes2((inPos0 + 2).toInt))
        assert(bytes((inPos0 + 3).toInt) == bytes2((inPos0 + 3).toInt))
        check(decIter1 == decIter2)
        check(pix1 == pix2)
      } else if (b1 == OpRgba) {
        assert(decIter1.inPos == inPos0 + 5)
        assert(bytes((inPos0 + 1).toInt) == bytes2((inPos0 + 1).toInt))
        assert(bytes((inPos0 + 2).toInt) == bytes2((inPos0 + 2).toInt))
        assert(bytes((inPos0 + 3).toInt) == bytes2((inPos0 + 3).toInt))
        assert(bytes((inPos0 + 4).toInt) == bytes2((inPos0 + 4).toInt))
        check(decIter1 == decIter2)
        check(pix1 == pix2)
      } else if ((b1 & Mask2) == OpLuma) {
        assert(decIter1.inPos == inPos0 + 2)
        assert(bytes((inPos0 + 1).toInt) == bytes2((inPos0 + 1).toInt))
        check(decIter1 == decIter2)
        check(pix1 == pix2)
      } else if ((b1 & Mask2) == OpIndex || (b1 & Mask2) == OpDiff) {
        assert(decIter1.inPos == inPos0 + 1)
        check(decIter1 == decIter2)
        check(pix1 == pix2)
      } else if ((b1 & Mask2) == OpRun) {
        assert(decIter1.inPos == inPos0 + 1)
        assert(res1 == Run(decodeRun(b1)))
        assert(res2 == Run(decodeRun(b1)))
        // TODO: Not so fast!! These require more than what they look!!
        // TODO: Timeout
        check(decIter1 == decIter2)
        check(pix1 == pix2)
      } else {
        assert(res1 == DiffIndexColor(pxPrev))
        assert(res2 == DiffIndexColor(pxPrev))
        assert(decIter1.inPos == inPos0 + 1)
        check(decIter1 == decIter2)
        check(pix1 == pix2)
      }
      check(decIter1 == decIter2)
      check(pix1 == pix2)
    }.ensuring { _ =>
      res1 == res2 &&&
      ix1 == ix2 &&&
      pix1 == pix2 &&&
      decIter1 == decIter2
    }
  }

  // OK
  @opaque
  @inlineOnce
  @pure
  def doDecodeNextBytesEqLemma(index: Array[Int], pxPrev: Int, inPos0: Long, bytes2: Array[Byte])(using ctx1: Ctx): Unit = {
    require(index.length == 64)
    require(inPosInv(inPos0))
    require(inPos0 < chunksLen)
    require(bytes.length == bytes2.length)

    val ctx2 = Ctx(freshCopy(bytes2), w, h, chan)
    val (res1, inPos1) = doDecodeNext(index, pxPrev, inPos0)(using ctx1)
    require(arraysEq(bytes, bytes2, inPos0, inPos1))
    val (res2, inPos2) = doDecodeNext(index, pxPrev, inPos0)(using ctx2)

    {
      assert(bytes(inPos0.toInt) == bytes2(inPos0.toInt))
      check(inPos1 == inPos2)
      check(res1 == res2) // smt-z3 struggles here, use smt-cvc4 for this one
      ()
    }.ensuring { _ =>
      res1 == res2 &&&
      inPos1 == inPos2
    }
  }

  /////////////////////////////////////////////////////////////////////////////////////////////////////

  @inline
  def w(using ctx: Ctx): Long = ctx.w

  @inline
  def h(using ctx: Ctx): Long = ctx.h

  @inline
  def chan(using ctx: Ctx): Long = ctx.chan

  @inline
  def pixelsLen(using ctx: Ctx): Long = ctx.pixelsLen

  @inline
  def chunksLen(using ctx: Ctx): Long = ctx.chunksLen

  @inline
  def bytes(using ctx: Ctx): Array[Byte] = ctx.bytes
}
