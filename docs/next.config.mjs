import nextra from 'nextra'

const basePath = process.env.NODE_ENV === 'production' ? '/ligature' : ''

const withNextra = nextra({
  latex: true,
  search: {
    codeblocks: false
  },
})

const config = {
  basePath,
  experimental: {
    optimizePackageImports: false,
  },
  images: {
    unoptimized: true,
  },
}

// Only use static export in production
if (process.env.NODE_ENV === 'production') {
  config.output = 'export'
}

export default withNextra(config)