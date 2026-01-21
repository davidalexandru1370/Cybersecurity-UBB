package com.example.backend.business.service;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.security.crypto.bcrypt.BCryptPasswordEncoder;
import org.springframework.stereotype.Service;

import com.example.backend.business.entities.CreateUserDTO;
import com.example.backend.business.repository.UserRepository;
import com.example.backend.business.service.interfaces.IUserService;
import com.example.backend.core.domain.User;
import com.example.backend.core.enums.TokenType;
import com.example.backend.core.exceptions.ExistingAccountException;
import com.example.backend.core.exceptions.ExpiredTokenException;
import com.example.backend.core.exceptions.NotFoundException;

import io.jsonwebtoken.Claims;
import io.jsonwebtoken.ExpiredJwtException;
import io.jsonwebtoken.Jwts;
import io.jsonwebtoken.MalformedJwtException;
import io.jsonwebtoken.UnsupportedJwtException;
import io.jsonwebtoken.security.Keys;

import java.util.Date;

import javax.crypto.SecretKey;

@Service
public class UserService implements IUserService {

    @Autowired
    private UserRepository userRepository;

    private final BCryptPasswordEncoder passwordEncoder = new BCryptPasswordEncoder(12);

    @Value("${jwt.secret}")
    private String jwtSecret;

    @Value("${jwt.refresh-secret}")
    private String jwtRefreshSecret;

    @Value("${jwt.expiration-ms:3600000}")
    private long jwtExpirationMs;

    @Override
    public User createUser(CreateUserDTO createUserDTO) throws ExistingAccountException {
        var existingUser = userRepository.findByEmail(createUserDTO.getEmail());

        if (existingUser != null) {
            throw new ExistingAccountException("User with email " + createUserDTO.getEmail() + " already exists.");
        }

        var encryptedPassword = passwordEncoder.encode(createUserDTO.getPassword());
        User newUser = new User(createUserDTO.getEmail(), encryptedPassword, createUserDTO.getRole());

        return userRepository.save(newUser);
    }

    @Override
    public User getUserByEmail(String email) {
        return userRepository.findByEmail(email);
    }

    @Override
    public boolean validateUserCredentials(String email, String password) {
        User user = userRepository.findByEmail(email);
        if (user != null && passwordEncoder.matches(password, user.getPassword())) {
            return true;
        }
        return false;
    }

    @Override
    public String generateAuthToken(String email, Long id) {
        long now = System.currentTimeMillis();
        Date issuedAt = new Date(now);
        Date expiry = new Date(now + jwtExpirationMs);
        var secretKey = getAccessTokenSecretKey(this.jwtSecret);

        String token = Jwts.builder()
                .subject(email)
                .claim("id", id)
                .issuedAt(issuedAt)
                .expiration(expiry)
                .signWith(secretKey)
                .compact();

        return token;
    }

    @Override
    public String generateRefreshToken(String email, Long id) {
        long now = System.currentTimeMillis();
        Date issuedAt = new Date(now);
        Date expiry = new Date(now + jwtExpirationMs * 24); // Refresh token valid for 24 times longer
        var secretKey = getRefreshTokenSecretKey(this.jwtSecret);

        String token = Jwts.builder()
                .subject(email)
                .claim("id", id)
                .issuedAt(issuedAt)
                .expiration(expiry)
                .signWith(secretKey)
                .compact();

        return token;
    }

    @Override
    public Boolean validateToken(String token, TokenType tokenType) throws ExpiredTokenException {
        try {
            SecretKey key = getAccessTokenSecretKey(this.jwtSecret);
            if (tokenType == TokenType.REFRESH) {
                key = getRefreshTokenSecretKey(this.jwtRefreshSecret);
            }
            Jwts.parser().decryptWith(key).build().parseSignedClaims(token);
            return true;
        } catch (SecurityException | MalformedJwtException e) {
            throw new ExpiredTokenException("JWT was expired or incorrect");
        } catch (ExpiredJwtException e) {
            throw new ExpiredTokenException("Expired JWT token.");
        } catch (UnsupportedJwtException e) {
            throw new ExpiredTokenException("Unsupported JWT token.");
        } catch (IllegalArgumentException e) {
            throw new ExpiredTokenException("JWT token compact of handler are invalid.");
        }
    }

    @Override
    public Long getIdFromToken(String token, TokenType tokenType) {
        var secretKey = getAccessTokenSecretKey(this.jwtSecret);
        if (tokenType == TokenType.REFRESH) {
            secretKey = getRefreshTokenSecretKey(this.jwtRefreshSecret);
        }
        Claims claims = Jwts.parser().verifyWith(secretKey).build().parseSignedClaims(token).getPayload();
        return claims.get("id", Long.class);
    }

    private SecretKey getAccessTokenSecretKey(String secret) {
        byte[] keyBytes = secret.getBytes();
        return Keys.hmacShaKeyFor(keyBytes);
    }

    private SecretKey getRefreshTokenSecretKey(String secret) {
        byte[] keyBytes = secret.getBytes();
        return Keys.hmacShaKeyFor(keyBytes);
    }

    @Override
    public User getUserById(Long id) throws NotFoundException {
        var user = userRepository.findById(id);
        if (user.isPresent()) {
            return user.get();
        }

        throw new NotFoundException("User does not exist");
    }

}
