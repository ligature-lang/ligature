/* eslint-env node */
import { Footer, Layout, Navbar } from 'nextra-theme-docs'
import { Banner, Head } from 'nextra/components'
import { getPageMap } from 'nextra/page-map'
import 'nextra-theme-docs/style.css'

export const metadata = {
  metadataBase: new URL('https://github.com/ligature-lang/ligature'),
  title: {
    template: '%s - Ligature'
  },
  description: 'Ligature: a configuration language you can trust',
  applicationName: 'Ligature',
  generator: 'Next.js',
  appleWebApp: {
    title: 'Ligature'
  },
  other: {
    'msapplication-TileImage': '/ms-icon-144x144.png',
    'msapplication-TileColor': '#fff'
  }
}

export default async function RootLayout({ children }) {
  const navbar = (
    <Navbar
      logo={
        <div>
          <b>Ligature</b>{' '}
          <span style={{ opacity: '60%' }}>Typed Configuration</span>
        </div>
      }
      // TODO: include discord or slack server here
      // chatLink="https://discord.gg/hEM84NMkRv"
    />
  )
  const pageMap = await getPageMap()
  return (
    <html lang="en" dir="ltr" suppressHydrationWarning>
      <Head faviconGlyph="✦" />
      <body>
        <Layout
          banner={<Banner storageKey="Ligature">Ligature is available in alpha on crates.io!</Banner>}
          navbar={navbar}
          footer={<Footer>Apache 2.0 {new Date().getFullYear()} © Cory Parent.</Footer>}
          editLink="Edit this page on GitHub"
          docsRepositoryBase="https://github.com/ligature-lang/ligature/blob/main/docs"
          sidebar={{ defaultMenuCollapseLevel: 1 }}
          pageMap={pageMap}
        >
          {children}
        </Layout>
      </body>
    </html>
  )
}