// Package palette maps pixels onto a fixed color palette.
//
// Each palette is a list of sRGB colors. The nearest color is the one
// with the smallest squared Euclidean distance in RGB. Equal distances
// keep the earlier palette entry.
package palette
