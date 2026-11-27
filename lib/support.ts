/** Where the Support button sends people: a Stripe Payment Link with "customer chooses the amount"
 *  (NEXT_PUBLIC_SUPPORT_URL), else the sponsor link, else nothing (the page explains how to help otherwise). */
export const SUPPORT_URL: string | null = process.env.NEXT_PUBLIC_SUPPORT_URL || process.env.NEXT_PUBLIC_SPONSOR_URL || null;
/** GitHub Sponsors profile of the maintainer: where most agent owners already have a payment method. */
export const GITHUB_SPONSORS_URL = process.env.NEXT_PUBLIC_GITHUB_SPONSORS_URL || "https://github.com/sponsors/GuillaumeBAUD-coder";
